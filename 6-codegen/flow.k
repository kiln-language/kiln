// The optimizations that look past one basic block: constants, addresses, redundant loads, and
// branches (bounds checks among them) that what is already known decides.
//
// `opt.k` works inside a block or from use counts. This file builds the function's control-flow
// graph and runs one forward dataflow over it, "what is known on entry to each block", to a
// fixpoint. It runs once, after inlining (main.k), where the accessors a loop calls (`Vec.get`,
// `Vec.set`, `Vec.at`) have been spliced into it and their checks sit beside the loop's own
// condition. Per function, in order:
//
//   foldConstants   an operation on constants becomes a constant, computed at the operation's
//                   width and signedness exactly as the emitter would; x+0, x*1, x&0 and the
//                   rest of the identities; x * 2^k a shift; a read of an immutable global whose
//                   value is known its value; a branch on constants a jump, or nothing.
//   foldAddresses   [t + o] where t = x + k in the same block: [x + k + o]. One instruction fewer,
//                   and two reads of one field through one pointer now name the same place.
//   the dataflow    a fact is a relation between a temp and a temp or a constant, which a branch
//                   establishes on the edge it takes (or does not take) and a passed `Bounds`
//                   check after it; or "this memory location holds this temp", which a load or a
//                   store establishes. A fact holds on entry to a block when it holds at the end
//                   of every edge into it. A definition of a temp ends every fact naming it; a
//                   store that may write the location ends a memory fact, and so does a call or
//                   an `asm` block, unless the location is a frame slot nothing else can reach.
//   rewrite         a load whose location's value is known becomes a copy of the temp holding it
//                   (redundant-load elimination and store-to-load forwarding); a branch or a
//                   bounds check the facts decide becomes a jump or nothing; a signed division or
//                   remainder by 2^k of a value that is never negative becomes a shift or a mask.
//   unreachable     what no path reaches any more (a removed check's panic, mostly) goes.
//
// Soundness. A fact is generated only by an instruction that makes it true (the edge of a branch,
// a check that passed, a load, a store) and dropped at anything that could make it false, and a
// block's facts are the ones true on EVERY path into it; a call that never returns (`noReturn`)
// has no path out. So a removed check is one that could not have failed, and a removed load one
// whose value was already in hand. Where the pass is unsure it keeps the instruction: a location
// reached through a pointer may be any other such location, any global and any slot whose address
// was ever handed on; a sum is trusted not to wrap only when a fact bounds it.
#include <{ir, opt}>
#include <parse::types>
#include <transform::eval>
#include <support::{compiler, fp}>
#include <stdlib::{fmt, map, option, string, vec}>

// The four bitsets each block has, at four consecutive strides of the function's word array.
local SET_IN: long = 0;
local SET_OUT: long = 1;
local SET_GEN: long = 2;
local SET_KILL: long = 3;

// A fact is a relation, or a memory location's value.
local F_REL: long = 0;
local F_MEM: long = 1;
local F_EXPR: long = 2;     // a temp holds the value of an expression (common subexpressions)

// How a predecessor reaches a block: through the branch at its end, or by falling through.
local E_TAKEN: long = 0;
local E_FALL: long = 1;

// What a location is relative to: a temp's value (any pointer), a frame slot, or a global.
local R_TEMP: long = 0;
local R_SLOT: long = 1;
local R_GLOBAL: long = 2;

// One function's dataflow is skipped when its bitsets would pass this many bits: a function with
// thousands of blocks and thousands of facts, of which this compiler has a handful. They keep
// every other pass.
local MAX_FLOW_BITS: long = 1 << 23;

// Where the hidden scratch slots' numbers start among the roots, past any name's.
local AGG_BASE: long = 1099511627776;      // 2^40, past every name's number

local LONG_MAX: long = 9223372036854775807;
local LONG_MIN: long = 0 - 9223372036854775807 - 1;
local IMM_LO: long = 0 - 2147483648;
local IMM_HI: long = 2147483647;

pub struct Flow {
    op: Opt,

    // The function being worked on: its instruction run and its temp range. Every per-temp
    // vector is indexed by `t - base`.
    first: long, n: long, base: Temp, nt: long,

    defs: Vec<long>,          // how many instructions write each temp
    defAt: Vec<long>,         // the one that does, when exactly one does (relative index)
    // Constants known within the current block for a temp with several definitions, and the
    // last place each temp was written in it: valid while the stamp is the block's.
    kStamp: Vec<long>, kVal: Vec<long>,
    dStamp: Vec<long>, dPos: Vec<long>,
    nonneg: Vec<bool>,        // every definition of the temp yields a value >= 0
    // An address constant: a temp whose one definition is `&slot` plus a constant, so it holds
    // the same address wherever it holds anything.
    acRoot: Vec<long>, acKind: Vec<long>, acOff: Vec<long>,
    exposed: HashMap<long, bool>,   // slots whose address went somewhere this pass cannot follow
    globalAt: HashMap<long, long>,  // a global's name -> its index in the program's tables

    // The graph. Instruction indexes are relative to `first`.
    bStart: Vec<long>, bEnd: Vec<long>,
    bTaken: Vec<long>, bFall: Vec<long>,     // successor blocks, or -1
    bCond: Vec<long>, bNeg: Vec<long>,       // the fact the taken / fallthrough edge adds, or -1
    blockOf: Vec<long>,
    predFirst: Vec<long>, predCount: Vec<long>, predBlock: Vec<long>, predKind: Vec<long>,
    order: Vec<long>,                        // reverse postorder of the reachable blocks
    reach: Vec<bool>,
    labelAt: HashMap<long, long>,
    stack: Vec<long>, stackNext: Vec<long>,

    // The facts.
    fKind: Vec<long>, fOp: Vec<IROp>, fA: Vec<Temp>, fB: Vec<Temp>, fImm: Vec<long>,
    fIsImm: Vec<bool>, fUns: Vec<bool>, fLoc: Vec<long>,
    factKey: HashMap<long, long>,
    // Memory locations: (root kind, root, offset, width) and the load class (width and how it
    // extends) a value read there has.
    lRootKind: Vec<long>, lRoot: Vec<long>, lOff: Vec<long>, lWidth: Vec<long>, lCls: Vec<long>,
    locKey: HashMap<long, long>,
    instLoc: Vec<long>,       // per instruction: the location it reads or writes, or -1
    instFact: Vec<long>,      // per instruction: the fact it establishes inside its block, or -1
    // Facts by the temps they name, as runs in one flat list.
    tfFirst: Vec<long>, tfCount: Vec<long>, tfList: Vec<long>,
    callKill: Vec<long>, allMem: Vec<long>,   // bitsets: what a call ends, what `asm` ends
    tempMem: Vec<long>,                      // and the memory facts reached through a pointer
    // Roots (rk, root) by key, each with its locations as a list (`rootHead`, `locNext`); each
    // location with its memory facts as a list (`locFactHead`, `factNext`).
    rootKey: HashMap<long, long>, rRk: Vec<long>, rRoot: Vec<long>, rootHead: Vec<long>,
    locNext: Vec<long>, locFactHead: Vec<long>, factNext: Vec<long>, keep: Vec<long>,
    words: long, nf: long,
    bits: Vec<long>,
    cur: Vec<long>,
    addOk: Vec<bool>,         // per instruction: its `+`, `*` or `<<` cannot wrap when its operands are never negative
    condHi: Vec<long>,        // per single-definition temp: its upper bound, on that same condition (`boundWalk`)
    transDepth: long,         // `decide` through a third temp, not twice over
    // Per block copy, its (source fact, destination fact) pairs as a run; and per block whether
    // one is in it.
    cmFirst: Vec<long>, cmCount: Vec<long>, cmSrc: Vec<long>, cmDst: Vec<long>, cmOn: Vec<bool>,
    copies: Vec<long>, copyAt: HashMap<long, long>, needNonneg: bool,
    bDyn: Vec<bool>,
    // Jump threading: each edge's decision into the block being threaded, the blocks a round
    // already changed, and the labels it made.
    tDec: Vec<long>, tDirty: Vec<bool>, tConst: Vec<bool>, threadSeq: long, tConstReady: bool,

    // Scratch for a constant read out of an operand, and an interval read out of the facts.
    cv: long, lo: long, hi: long,
    // Copies seen in the block being walked (`noteCopy`).
    eqTo: Vec<long>, eqStamp: Vec<long>, eqPos: Vec<long>, walkStamp: long,

    nFolded: long, nAddr: long, nLoads: long, nBranches: long, nChecks: long, nUnreach: long,
    nStrength: long, nSkipped: long, nMovs: long, nDead: long, nThreads: long, nDeadStores: long, nShared: long,
    slotRead: HashMap<long, bool>,     // `dropDeadSlots`: the frame slots something reads
    // Common subexpressions (`exprFacts`): per instruction its expression group or -1; per group
    // the expression and its facts as a list (`eHead`, `eNext`); the counting by shape.
    instExpr: Vec<long>, shapeOf: Vec<long>, shapeCount: HashMap<long, long>, eKey: HashMap<long, long>,
    eOp: Vec<IROp>, eA: Vec<Temp>, eB: Vec<Temp>, eImm: Vec<long>, eIsImm: Vec<bool>,
    eKind: Vec<Lit>, eFrom: Vec<Lit>, eTo: Vec<Lit>, eHead: Vec<long>, eNext: Vec<long>, nCse: long,
    // The counters as this function began, so the cleanup knows what it has to do.
    mark0: long, mark1: long, mark2: long, mark3: long
}

pub var gFlowOff: bool = false;
pub var gThreadOff: bool = false;     // `--no-thread`: the dataflow without jump threading
pub var gCseOff: bool = false;        // `--no-cse`: the dataflow without common subexpressions

methods Flow for Default {
    new -> Flow {
        return Flow { op: Opt.new(), first: 0, n: 0, base: 0, nt: 0,
                      defs: vec![], defAt: vec![], kStamp: vec![], kVal: vec![], dStamp: vec![], dPos: vec![],
                      nonneg: vec![], acRoot: vec![], acKind: vec![], acOff: vec![], exposed: map![], globalAt: map![],
                      bStart: vec![], bEnd: vec![], bTaken: vec![], bFall: vec![], bCond: vec![], bNeg: vec![],
                      blockOf: vec![], predFirst: vec![], predCount: vec![], predBlock: vec![], predKind: vec![],
                      order: vec![], reach: vec![], labelAt: map![], stack: vec![], stackNext: vec![],
                      fKind: vec![], fOp: vec![], fA: vec![], fB: vec![], fImm: vec![], fIsImm: vec![], fUns: vec![],
                      fLoc: vec![], factKey: map![],
                      lRootKind: vec![], lRoot: vec![], lOff: vec![], lWidth: vec![], lCls: vec![], locKey: map![],
                      instLoc: vec![], instFact: vec![],
                      tfFirst: vec![], tfCount: vec![], tfList: vec![], callKill: vec![], allMem: vec![], tempMem: vec![],
                      rootKey: map![], rRk: vec![], rRoot: vec![], rootHead: vec![], locNext: vec![],
                      locFactHead: vec![], factNext: vec![], keep: vec![],
                      words: 0, nf: 0, bits: vec![], cur: vec![], addOk: vec![], condHi: vec![], transDepth: 0,
                      cmFirst: vec![], cmCount: vec![], cmSrc: vec![], cmDst: vec![], cmOn: vec![], bDyn: vec![],
                      copies: vec![], copyAt: map![], needNonneg: false, tDec: vec![], tDirty: vec![], tConst: vec![], threadSeq: 0, tConstReady: false,
                      cv: 0, lo: 0, hi: 0, eqTo: vec![], eqStamp: vec![], eqPos: vec![], walkStamp: 0,
                      nFolded: 0, nAddr: 0, nLoads: 0, nBranches: 0, nChecks: 0, nUnreach: 0, nStrength: 0, nSkipped: 0, nMovs: 0, nDead: 0, nThreads: 0, nDeadStores: 0, nShared: 0, slotRead: map![],
                      instExpr: vec![], shapeOf: vec![], shapeCount: map![], eKey: map![], eOp: vec![], eA: vec![], eB: vec![],
                      eImm: vec![], eIsImm: vec![], eKind: vec![], eFrom: vec![], eTo: vec![], eHead: vec![], eNext: vec![], nCse: 0, mark0: 0, mark1: 0, mark2: 0, mark3: 0 };
    }
}

methods Flow {
    run &self inout p:IRProgram -> void {
        if (gFlowOff) { return; }
        self.globalAt.clear();
        for g in 0..p.globals.len() { self.globalAt.put(p.globals.get(g) as long, g); }
        for f in 0..p.funcs.len() { self.runOne(p, p.funcs.get(f)); }
        if (gTraceOpt) {
            eprintln("flow: {} folded, {} strength-reduced, {} addresses, {} loads, {} branches, {} checks, {} edges threaded, {} unreachable, {} dead stores, {} common subexpressions, {} copies shared, {} functions skipped",
                     self.nFolded, self.nStrength, self.nAddr, self.nLoads, self.nBranches, self.nChecks, self.nThreads, self.nUnreach, self.nDeadStores, self.nCse, self.nShared, self.nSkipped);
        }
    }

    runOne &self inout p:IRProgram fn:IRFunc -> void {
        if (fn.instrCount == 0) { return; }
        self.first = fn.firstInstr;
        self.n = fn.instrCount;
        self.base = fn.firstTemp;
        self.nt = fn.tempCount - fn.firstTemp;
        if (self.nt < 0) { self.nt = 0; }
        if (!self.wellFormed(p)) { self.nSkipped = self.nSkipped + 1; return; }
        self.mark0 = self.nMovs;
        self.mark1 = self.nFolded + self.nStrength;
        self.mark2 = self.nBranches + self.nChecks + self.nThreads;
        self.mark3 = self.nLoads + self.nFolded + self.nStrength + self.nAddr + self.nBranches + self.nChecks + self.nUnreach + self.nThreads + self.nDeadStores + self.nCse + self.nShared;
        self.countDefs(p);
        self.foldConstants(p);
        self.foldAddresses(p);
        self.shareCopies(p);
        self.buildBlocks(p);
        self.removeUnreachable(p);
        self.thread(p);
        if (self.collectFacts(p)) {
            self.solve(p);
            // Only a comparison with a constant, a bounds check or a division asks whether a
            // value can be negative.
            self.nonneg.clear();
            if (self.needNonneg) {
                self.boundWalk(p);
                self.computeNonneg(p);
            }
            before: long = self.nLoads + self.nBranches + self.nChecks + self.nStrength;
            self.rewrite(p);
            // A load that became a copy of a constant makes what reads it foldable in turn, and a
            // decided branch leaves code no path reaches.
            if (self.nLoads + self.nBranches + self.nChecks + self.nStrength > before) {
                self.foldConstants(p);
                self.buildBlocks(p);
                self.removeUnreachable(p);
            }
        } else {
            self.nSkipped = self.nSkipped + 1;
        }
        self.dropDeadSlots(p);
        // What the rewrites leave: copies to propagate, constants to carry as immediates, jumps to
        // nowhere, dead definitions. Each only where this function had a rewrite that leaves one.
        self.op.base = fn.firstTemp;
        if (self.nMovs > self.mark0) { self.op.propagateCopies(p, fn); }
        if (self.nFolded + self.nStrength > self.mark1) { self.op.selectImmediates(p, fn); }
        if (self.nBranches + self.nChecks + self.nThreads > self.mark2) { self.op.simplifyJumps(p, fn); }
        if (self.nLoads + self.nFolded + self.nStrength + self.nAddr + self.nBranches + self.nChecks + self.nUnreach + self.nThreads + self.nDeadStores + self.nCse + self.nShared > self.mark3) {
            self.sweep(p);
        }
        // A block threading left holding a constant it tested, dead now and swept, is one more
        // block of nothing but a branch.
    }

    // Every instruction whose result nothing reads and which does nothing else, as `dropDeadDefs`
    // does, but in one pass and a worklist: a removed instruction's operands lose a reader, and a
    // temp left with none takes its single definition with it. A temp with several definitions
    // is left to the next scan, which runs only while the last one found something.
    sweep &self inout p:IRProgram -> void {
        fillLong(&self.dStamp, self.nt, 0);      // here, each temp's readers
        for i in 0..self.n {
            ix: long = self.first + i;
            if (p.code[ix].op == IROp.Nop) { continue; }
            self.countUse(p.code[ix].a, 1);
            if (!p.code[ix].bIsImm) { self.countUse(p.code[ix].b, 1); }
            in: Instr = p.code.get(ix);
            for k in 0..in.argCount { self.countUse(p.args.get(in.firstArg + k), 1); }
            for k in 0..in.pieceCount { self.countUse(p.asmVals.get(in.firstPiece + k), 1); }
        }
        going: bool = true;
        while (going) {
            going = false;
            self.keep.clear();
            for i in 0..self.n { if (self.deadAt(p, i)) { self.keep.push(i); } }
            while (self.keep.len() > 0) {
                i: long = self.keep.pop();
                if (!self.deadAt(p, i)) { continue; }
                ix: long = self.first + i;
                a: Temp = p.code[ix].a;
                b: Temp = NO_TEMP;
                if (!p.code[ix].bIsImm) { b = p.code[ix].b; }
                p.code.set(ix, instr(IROp.Nop));
                self.nDead = self.nDead + 1;
                going = true;
                self.release(p, a);
                if (b != a) { self.release(p, b); } else { self.countUse(b, -1); }
            }
        }
    }

    countUse &self t:Temp d:long -> void {
        r: long = self.rel(t);
        if (r >= 0) { self.dStamp.set(r, self.dStamp.get(r) + d); }
    }

    // One reader fewer; a temp left with none whose one definition is pure goes on the list.
    release &self inout p:IRProgram t:Temp -> void {
        r: long = self.rel(t);
        if (r < 0) { return; }
        self.dStamp.set(r, self.dStamp.get(r) - 1);
        if (self.dStamp.get(r) == 0 && self.defs.get(r) == 1 && self.defAt.get(r) >= 0) { self.keep.push(self.defAt.get(r)); }
    }

    deadAt &self inout p:IRProgram i:long -> bool {
        ix: long = self.first + i;
        o: IROp = p.code[ix].op;
        if (!pureResult(o) || p.code[ix].paramSeed) { return false; }
        r: long = self.rel(p.code[ix].dst);
        return r >= 0 && self.dStamp.get(r) == 0;
    }

    // Every operand an instruction reads is there. One that is missing is a construct the lowerer
    // does not support and lowered to nothing (a `double` literal is one): the emitter reads
    // whatever `rax` holds, and a function whose meaning is a register's leftovers is left exactly
    // as it is.
    wellFormed &self inout p:IRProgram -> bool {
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            o: IROp = in.op;
            bMissing: bool = !in.bIsImm && in.b == NO_TEMP;
            if (o == IROp.PtrStore || o == IROp.Jcc || isCompare(o) || isArith(o) || o == IROp.ArrStore
                || o == IROp.Bounds || o == IROp.AggCopy) {
                if (in.a == NO_TEMP || bMissing) { return false; }
            }
            if ((o == IROp.Mov || o == IROp.Store || o == IROp.Ret || o == IROp.Jz || o == IROp.Convert
                 || o == IROp.BNot || o == IROp.PtrLoad || o == IROp.AggZero) && in.a == NO_TEMP) { return false; }
            for k in 0..in.argCount { if (p.args.get(in.firstArg + k) == NO_TEMP) { return false; } }
        }
        return true;
    }

    // ─── temps ───────────────────────────────────────────────────────────────

    countDefs &self inout p:IRProgram -> void {
        fillLong(&self.defs, self.nt, 0);
        fillLong(&self.defAt, self.nt, -1);
        for i in 0..self.n {
            d: Temp = p.code.get(self.first + i).dst;
            r: long = d - self.base;
            if (d != NO_TEMP && r >= 0 && r < self.nt) {
                self.defs.set(r, self.defs.get(r) + 1);
                self.defAt.set(r, i);
            }
        }
    }

    // Our own temp, as an index, or -1.
    rel &self t:Temp -> long {
        if (t == NO_TEMP) { return -1; }
        r: long = t - self.base;
        if (r < 0 || r >= self.nt) { return -1; }
        return r;
    }

    // `t` is written by exactly one instruction, a `Const`: it holds that value wherever it holds
    // anything. The value is left in `cv`. (Stamp 0 asks for this kind alone: outside
    // `foldConstants` no block-local table is live.)
    singleConst &self inout p:IRProgram t:Temp -> bool {
        r: long = self.rel(t);
        if (r < 0 || self.defs.get(r) != 1) { return false; }
        d: Instr = p.code.get(self.first + self.defAt.get(r));
        if (d.op != IROp.Const) { return false; }
        self.cv = d.imm;
        return true;
    }

    // `t` as a constant at this point of the current block (`stamp`): one with a single `Const`
    // definition anywhere, or one the block itself just set.
    constAt &self inout p:IRProgram t:Temp stamp:long -> bool {
        if (self.singleConst(p, t)) { return true; }
        r: long = self.rel(t);
        if (stamp < 1 || r < 0 || self.kStamp.get(r) != stamp) { return false; }
        self.cv = self.kVal.get(r);
        return true;
    }

    // Operand `b` as a constant: the immediate it carries, or a constant temp.
    bConst &self inout p:IRProgram in:Instr stamp:long -> bool {
        if (in.bIsImm) { self.cv = in.bImm; return true; }
        if (in.b == NO_TEMP) { return false; }
        return self.constAt(p, in.b, stamp);
    }

    // ─── 1. constants ────────────────────────────────────────────────────────

    foldConstants &self inout p:IRProgram -> void {
        fillLong(&self.kStamp, self.nt, 0);
        fillLong(&self.kVal, self.nt, 0);
        stamp: long = 1;
        for i in 0..self.n {
            at: long = self.first + i;
            in: Instr = p.code.get(at);
            if (in.op == IROp.Label) { stamp = stamp + 1; continue; }
            if (in.op == IROp.Nop) { continue; }
            if (self.foldOne(p, &in, stamp)) {
                p.code.set(at, in);
                self.nFolded = self.nFolded + 1;
            }
            r: long = self.rel(in.dst);
            if (r >= 0) {
                if (in.op == IROp.Const) { self.kStamp.set(r, stamp); self.kVal.set(r, in.imm); }
                else { self.kStamp.set(r, 0); }
            }
        }
    }

    // Rewrites `in` in place when it folds; says whether it did.
    foldOne &self inout p:IRProgram inout in:Instr stamp:long -> bool {
        o: IROp = in.op;
        if (o == IROp.Const) { return false; }
        // A read of an immutable global whose initializer folded to a number: `.rodata` holds that
        // number for the whole run, and nothing can write it (a write would fault).
        if (o == IROp.Load) {
            if (!in.isGlobal || in.paramSeed || in.name == NO_SYM || !foldableKind(in.kind)) { return false; }
            hit: Option<long> = self.globalAt.find(in.name as long);
            g: long = -1;
            match hit { Some(x) { g = x; } None { return false; } }
            if (!p.globalHasInit.get(g) || p.globalImage.get(g) >= 0 || isVarGlobal(in.name)) { return false; }
            makeConst(in, canon(in.kind, p.globalInits.get(g)));
            return true;
        }
        if (o == IROp.Mov) {
            if (!self.constAt(p, in.a, stamp)) { return false; }
            makeConst(in, self.cv);
            return true;
        }
        if (o == IROp.Convert && (isFloatKind(in.fromKind) || isFloatKind(in.toKind))) {
            if (!self.constAt(p, in.a, stamp)) { return false; }
            fromK: Lit = in.fromKind;
            toK: Lit = in.toKind;
            if (!(isFloatKind(fromK) || foldableKind(fromK)) || !(isFloatKind(toK) || foldableKind(toK))) { return false; }
            makeConst(in, canon(toK, convertBits(self.cv, fromK, toK)));
            return true;
        }
        if (o == IROp.Convert) {
            // A backed enum or a distinct type is a `Lit.Struct` in a register, which the emitter
            // converts to and from as a full word: `2 as Meters` is 2.
            if (!convertible(in.fromKind) || !convertible(in.toKind)) { return false; }
            if (!self.constAt(p, in.a, stamp)) { return false; }
            makeConst(in, canon(in.toKind, self.cv));
            return true;
        }
        if (o == IROp.BNot) {
            if (!foldableKind(in.kind) || !self.constAt(p, in.a, stamp)) { return false; }
            makeConst(in, canon(in.kind, ~self.cv));
            return true;
        }
        if (o == IROp.Jz) {
            if (!self.constAt(p, in.a, stamp)) { return false; }
            self.decideBranch(in, self.cv == 0);
            return true;
        }
        if (o == IROp.Jcc) {
            if (!self.constAt(p, in.a, stamp)) { return false; }
            x: long = self.cv;
            if (!self.bConst(p, in, stamp)) { return false; }
            // A float branch with `imm` 1 jumps when the comparison does not hold (`fuseBranches`).
            if (isFloatKind(in.kind)) { self.decideBranch(in, fpCompare(fpOp(in.cmpOp), x, self.cv, in.kind == Lit.Float) != (in.imm == 1)); }
            else { self.decideBranch(in, compareHolds(in.cmpOp, x, self.cv, kindUnsigned(in.kind))); }
            return true;
        }
        if (isCompare(o)) {
            if (!self.constAt(p, in.a, stamp)) { return false; }
            x: long = self.cv;
            if (!self.bConst(p, in, stamp)) { return false; }
            if (isFloatKind(in.kind)) { makeConst(in, boolWord(fpCompare(fpOp(o), x, self.cv, in.kind == Lit.Float))); }
            else { makeConst(in, boolWord(compareHolds(o, x, self.cv, kindUnsigned(in.kind)))); }
            return true;
        }
        // Float arithmetic on constants, exactly as the SSE instruction computes it (`support::fp`
        // runs that instruction): no reassociation, no identity that is not one for every input
        // (`x + 0.0` is not `x` when x is -0.0), so nothing but the constant case folds.
        if (isFloatKind(in.kind) && (o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.Div || o == IROp.BXor)) {
            if (!self.constAt(p, in.a, stamp)) { return false; }
            x: long = self.cv;
            if (!self.bConst(p, in, stamp)) { return false; }
            single: bool = in.kind == Lit.Float;
            if (o == IROp.BXor) { makeConst(in, x ^ self.cv); return true; }
            ar: long = 0;
            if (o == IROp.Sub) { ar = 1; } else if (o == IROp.Mul) { ar = 2; } else if (o == IROp.Div) { ar = 3; }
            if (single) { makeConst(in, f32Arith(ar, x, self.cv)); } else { makeConst(in, f64Arith(ar, x, self.cv)); }
            return true;
        }
        if (!isArith(o) || !foldableKind(in.kind)) { return false; }
        ka: bool = self.constAt(p, in.a, stamp);
        x: long = self.cv;
        kb: bool = self.bConst(p, in, stamp);
        y: long = self.cv;
        if (ka && kb) {
            if (!self.evalArith(o, x, y, in.kind, in.bIsImm)) { return false; }
            makeConst(in, self.cv);
            return true;
        }
        if (!ka && !kb) { return false; }
        return self.identity(p, in, ka, x, kb, y);
    }

    // One operand constant: the algebraic identities, and a multiply by a power of two as a
    // shift. A result that becomes a copy of the other operand needs no re-extension, which holds
    // when the operation is a full word or the operand already has the operation's type.
    identity &self inout p:IRProgram inout in:Instr ka:bool x:long kb:bool y:long -> bool {
        o: IROp = in.op;
        sameWidth: bool = kindWidth(in.kind) == 8;
        if (o == IROp.Mul) {
            if ((kb && y == 0) || (ka && x == 0)) { makeConst(in, 0); return true; }
            if (kb && y == 1 && (sameWidth || p.kindOf(in.a) == in.kind)) { makeMov(in, in.a); self.nMovs = self.nMovs + 1; return true; }
            if (ka && x == 1 && !in.bIsImm && (sameWidth || p.kindOf(in.b) == in.kind)) { makeMov(in, in.b); self.nMovs = self.nMovs + 1; return true; }
            // x * 2^k is x << k: the same low 64 bits, re-extended the same way.
            other: Temp = NO_TEMP;
            c: long = 0;
            if (kb) { other = in.a; c = y; } else if (!in.bIsImm) { other = in.b; c = x; }
            k: long = log2Exact(c);
            if (other == NO_TEMP || k < 1) { return false; }
            in.op = IROp.Shl;
            in.a = other;
            in.b = NO_TEMP;
            in.bIsImm = true;
            in.bImm = k;
            self.nStrength = self.nStrength + 1;
            return true;
        }
        if (!kb) {
            if (o == IROp.Add && x == 0 && !in.bIsImm && (sameWidth || p.kindOf(in.b) == in.kind)) { makeMov(in, in.b); self.nMovs = self.nMovs + 1; return true; }
            if (o == IROp.BAnd && x == 0) { makeConst(in, 0); return true; }
            return false;
        }
        keep: bool = sameWidth || p.kindOf(in.a) == in.kind;
        if (y == 0 && (o == IROp.Add || o == IROp.Sub || o == IROp.BOr || o == IROp.BXor
                       || o == IROp.Shl || o == IROp.Shr) && keep) { makeMov(in, in.a); self.nMovs = self.nMovs + 1; return true; }
        if (o == IROp.BAnd && y == 0) { makeConst(in, 0); return true; }
        if (o == IROp.BAnd && y == -1 && keep) { makeMov(in, in.a); self.nMovs = self.nMovs + 1; return true; }
        if (o == IROp.Div && y == 1 && keep) { makeMov(in, in.a); self.nMovs = self.nMovs + 1; return true; }
        if (o == IROp.Mod && y == 1) { makeConst(in, 0); return true; }
        // An unsigned division by 2^k is a logical shift, its remainder a mask. A signed one waits
        // for `rewrite`, which knows which dividends are never negative.
        k: long = log2Exact(y);
        if (k >= 1 && kindUnsigned(in.kind) && (o == IROp.Div || o == IROp.Mod)) {
            if (o == IROp.Div) { in.op = IROp.Shr; in.bImm = k; }
            else {
                if (y - 1 > IMM_HI) { return false; }
                in.op = IROp.BAnd;
                in.bImm = y - 1;
            }
            in.b = NO_TEMP;
            in.bIsImm = true;
            self.nStrength = self.nStrength + 1;
            return true;
        }
        // Any other division or remainder by a constant from 2 to 2^31 - 1: the divisor rides on
        // the instruction, and the emitter divides by multiplying (`emitDivideConst`). The rest
        // (0, -1, which the machine must still fault or wrap on, and the negatives) stay `idiv`.
        if ((o == IROp.Div || o == IROp.Mod) && !in.bIsImm && y >= 2 && y <= IMM_HI
            && in.kind != Lit.Bool && in.kind != Lit.Ptr && in.kind != Lit.Ref) {
            in.b = NO_TEMP;
            in.bIsImm = true;
            in.bImm = y;
            self.nStrength = self.nStrength + 1;
            return true;
        }
        return false;
    }

    // A branch whose outcome is known: a jump when it is taken, nothing when it is not.
    decideBranch &self inout in:Instr taken:bool -> void {
        name: Sym = in.name;
        if (taken) { in = instr(IROp.Jmp); in.name = name; }
        else { in = instr(IROp.Nop); }
        self.nBranches = self.nBranches + 1;
    }

    // ─── 2. addresses ────────────────────────────────────────────────────────

    // `t = x + k; ... [t + o]` within one block, with `x` not written in between and `t` written
    // nowhere else: `[x + k + o]`. Repeated, so a chain of offsets collapses.
    foldAddresses &self inout p:IRProgram -> void {
        fillLong(&self.dStamp, self.nt, 0);
        fillLong(&self.dPos, self.nt, -1);
        stamp: long = 1;
        for i in 0..self.n {
            at: long = self.first + i;
            in: Instr = p.code.get(at);
            if (in.op == IROp.Label) { stamp = stamp + 1; continue; }
            if ((in.op == IROp.PtrLoad || in.op == IROp.PtrStore) && in.a != NO_TEMP) {
                changed: bool = false;
                going: bool = true;
                while (going) {
                    going = false;
                    r: long = self.rel(in.a);
                    if (r >= 0 && self.defs.get(r) == 1 && self.dStamp.get(r) == stamp) {
                        d: long = self.defAt.get(r);
                        def: Instr = p.code.get(self.first + d);
                        if (def.op == IROp.Add && def.a != NO_TEMP && self.bConst(p, def, 0)) {
                            k: long = self.cv;
                            xr: long = self.rel(def.a);
                            unchanged: bool = xr < 0 || self.dStamp.get(xr) != stamp || self.dPos.get(xr) < d;
                            sum: long = in.imm + k;
                            if (unchanged && k >= IMM_LO && k <= IMM_HI && sum >= IMM_LO && sum <= IMM_HI) {
                                in.a = def.a;
                                in.imm = sum;
                                changed = true;
                                going = true;
                            }
                        }
                    }
                }
                if (changed) { p.code.set(at, in); self.nAddr = self.nAddr + 1; }
            }
            r2: long = self.rel(in.dst);
            if (r2 >= 0) { self.dStamp.set(r2, stamp); self.dPos.set(r2, i); }
        }
    }

    // ─── the graph ───────────────────────────────────────────────────────────

    buildBlocks &self inout p:IRProgram -> void {
        self.bStart.clear(); self.bEnd.clear(); self.bTaken.clear(); self.bFall.clear();
        self.bCond.clear(); self.bNeg.clear();
        if (self.labelAt.cap() > 512) { self.labelAt = map![]; } else { self.labelAt.clear(); }
        fillLong(&self.blockOf, self.n, -1);
        // Leaders: the first instruction, every label, whatever follows a transfer of control.
        startNext: bool = true;
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            if (in.op == IROp.Label || startNext) {
                if (self.bStart.len() > 0) { self.bEnd.push(i - 1); }
                self.bStart.push(i);
                startNext = false;
            }
            b: long = self.bStart.len() - 1;
            self.blockOf.set(i, b);
            if (in.op == IROp.Label) { self.labelAt.put(in.name as long, b); }
            if (isTerminator(in.op) || (in.op == IROp.Call && in.noReturn)) { startNext = true; }
        }
        self.bEnd.push(self.n - 1);
        nb: long = self.bStart.len();
        for b in 0..nb {
            taken: long = -1;
            fall: long = -1;
            if (b + 1 < nb) { fall = b + 1; }
            last: long = self.lastReal(p, b);
            if (last >= 0) {
                in: Instr = p.code.get(self.first + last);
                if (isBranch(in.op)) {
                    hit: Option<long> = self.labelAt.find(in.name as long);
                    match hit { Some(t) { taken = t; } None { } }
                    if (in.op == IROp.Jmp) { fall = -1; }
                } else if (in.op == IROp.Ret || in.op == IROp.RetVoid || (in.op == IROp.Call && in.noReturn)) {
                    fall = -1;
                }
            }
            self.bTaken.push(taken);
            self.bFall.push(fall);
            self.bCond.push(-1);
            self.bNeg.push(-1);
        }
        // Predecessors, as runs, each with the kind of edge it arrives by.
        fillLong(&self.predCount, nb, 0);
        for b in 0..nb {
            if (self.bTaken.get(b) >= 0) { self.predCount.set(self.bTaken.get(b), self.predCount.get(self.bTaken.get(b)) + 1); }
            if (self.bFall.get(b) >= 0) { self.predCount.set(self.bFall.get(b), self.predCount.get(self.bFall.get(b)) + 1); }
        }
        self.predFirst.clear();
        total: long = 0;
        for b in 0..nb { self.predFirst.push(total); total = total + self.predCount.get(b); }
        fillLong(&self.predBlock, total, 0);
        fillLong(&self.predKind, total, 0);
        fillLong(&self.predCount, nb, 0);
        for b in 0..nb {
            t: long = self.bTaken.get(b);
            if (t >= 0) { self.addPred(t, b, E_TAKEN); }
            f: long = self.bFall.get(b);
            if (f >= 0) { self.addPred(f, b, E_FALL); }
        }
        self.computeOrder();
    }

    // One past a block's last instruction.
    stopOf &self b:long -> long { return self.bEnd.get(b) + 1; }

    addPred &self to:long from:long kind:long -> void {
        at: long = self.predFirst.get(to) + self.predCount.get(to);
        self.predBlock.set(at, from);
        self.predKind.set(at, kind);
        self.predCount.set(to, self.predCount.get(to) + 1);
    }

    // The last instruction of a block that is not a deleted one, or -1.
    lastReal &self inout p:IRProgram b:long -> long {
        i: long = self.bEnd.get(b);
        s: long = self.bStart.get(b);
        while (i >= s) {
            if (p.code.get(self.first + i).op != IROp.Nop) { return i; }
            i = i - 1;
        }
        return -1;
    }

    // Reverse postorder from the entry, by an explicit stack; `reach` is what it visited.
    computeOrder &self -> void {
        nb: long = self.bStart.len();
        self.reach.clear();
        for b in 0..nb { self.reach.push(false); }
        self.order.clear();
        self.stack.clear();
        self.stackNext.clear();
        if (nb == 0) { return; }
        post: Vec<long>;
        self.stack.push(0);
        self.stackNext.push(0);
        self.reach.set(0, true);
        while (self.stack.len() > 0) {
            top: long = self.stack.len() - 1;
            b: long = self.stack.get(top);
            k: long = self.stackNext.get(top);
            self.stackNext.set(top, k + 1);
            s: long = -1;
            if (k == 0) { s = self.bFall.get(b); }
            else if (k == 1) { s = self.bTaken.get(b); }
            else {
                post.push(b);
                self.stack.pop();
                self.stackNext.pop();
                continue;
            }
            if (s >= 0 && !self.reach.get(s)) {
                self.reach.set(s, true);
                self.stack.push(s);
                self.stackNext.push(0);
            }
        }
        i: long = post.len();
        while (i > 0) { i = i - 1; self.order.push(post.get(i)); }
    }

    // Every instruction of a block no path from the entry reaches, labels and all. Whatever
    // branched to such a label was unreachable too.
    removeUnreachable &self inout p:IRProgram -> void {
        for b in 0..self.bStart.len() {
            if (self.reach.get(b)) { continue; }
            for i in self.bStart.get(b)..self.stopOf(b) {
                at: long = self.first + i;
                if (p.code.get(at).op != IROp.Nop) {
                    p.code.set(at, instr(IROp.Nop));
                    self.nUnreach = self.nUnreach + 1;
                }
            }
        }
    }

    // ─── jump threading ──────────────────────────────────────────────────────

    // A block that does nothing but branch (its label, then a `jz`, a `jcc` or a `jmp`) is
    // passed through by an edge into it that already decides where it goes: the predecessor
    // jumps straight to the branch's target, or to what follows the block. An edge decides it
    // when the tested temp's last definition before it is a constant (`b = const 1; jmp .L` ahead
    // of `.L: jz .M if !b`: the bool an inlined predicate hands back, which is what `?` through
    // `Try.isBreak` leaves), or when the predecessor's own branch tested the same thing; a `jmp`
    // is decided by every edge. When every edge into a conditional block is decided, the block is
    // rewritten in place, since nothing can be inserted here: its branch's slot becomes the label
    // the jumps to what follows it aim at, and the slot before it (its own label) the `jmp` a
    // fallthrough edge that goes to the taken target needs. The block then has no reader of the
    // temp, and the constants it tested die. Repeated while it finds something, a few rounds at
    // most, so a chain of such blocks collapses.
    thread &self inout p:IRProgram -> bool {
        any: bool = false;
        if (gThreadOff) { return false; }
        self.tConstReady = false;
        rounds: long = 0;
        going: bool = true;
        while (going && rounds < 4) {
            going = false;
            rounds = rounds + 1;
            nb: long = self.bStart.len();
            self.tDirty.clear();
            for b in 0..nb { self.tDirty.push(false); }
            // A block whose edges this round already moved is left to the next, which sees them
            // as they now are.
            for b in 1..nb {
                if (!self.reach.get(b) || self.tDirty.get(b)) { continue; }
                pf: long = self.predFirst.get(b);
                clean: bool = true;
                for k in 0..self.predCount.get(b) { if (self.tDirty.get(self.predBlock.get(pf + k))) { clean = false; } }
                if (!clean || !self.threadInto(p, b)) { continue; }
                going = true;
                self.tDirty.set(b, true);
                if (self.bTaken.get(b) >= 0) { self.tDirty.set(self.bTaken.get(b), true); }
                if (self.bFall.get(b) >= 0) { self.tDirty.set(self.bFall.get(b), true); }
                for k in 0..self.predCount.get(b) { self.tDirty.set(self.predBlock.get(pf + k), true); }
            }
            if (going) {
                any = true;
                self.buildBlocks(p);
                self.removeUnreachable(p);
            }
        }
        return any;
    }

    // Threads the edges into block `b` that decide its branch; whether it moved any.
    threadInto &self inout p:IRProgram b:long -> bool {
        // Its labels, then a branch (the block's end) or nothing more: read forwards, so a block
        // of real work is turned down at its first instruction.
        br: long = -1;
        i: long = self.bStart.get(b);
        e: long = self.stopOf(b);
        while (i < e) {
            o: IROp = p.code.get(self.first + i).op;
            if (o == IROp.Label) { br = i; }
            else if (o != IROp.Nop) {
                if (!isBranch(o)) { return false; }
                br = i;
                i = e;
            }
            i = i + 1;
        }
        if (br < 0) { return false; }
        bi: Instr = p.code.get(self.first + br);
        cond: bool = bi.op == IROp.Jz || (bi.op == IROp.Jcc && !isFloatKind(bi.kind) && bi.a != NO_TEMP);
        tb: long = self.bTaken.get(b);
        fb: long = self.bFall.get(b);
        // A block of nothing but its label goes on to the next one: a jump into it may as well
        // name the next one's label, when it has one.
        // Only where that skips a jump: a label falling into another names the same address.
        if (bi.op == IROp.Label) {
            if (fb < 0 || fb == b || !self.jumpOnly(p, fb)) { return false; }
            next: Sym = self.labelOf(p, fb);
            if (next == NO_SYM) { return false; }
            bi = instr(IROp.Jmp);
            bi.name = self.forward(p, next);
            if (bi.name == next) { return false; }
            tb = fb;
        }
        if (!cond && bi.op != IROp.Jmp) { return false; }
        if (tb < 0 || tb == b) { return false; }
        if (cond && (fb < 0 || fb == tb || fb == b)) { return false; }
        // What follows the block, if something already labels it.
        fallLabel: Sym = NO_SYM;
        if (cond) { fallLabel = self.labelOf(p, fb); }
        pf: long = self.predFirst.get(b);
        pc: long = self.predCount.get(b);
        self.tDec.clear();
        all: bool = cond;
        for k in 0..pc {
            pb: long = self.predBlock.get(pf + k);
            d: long = -1;
            if (!self.reach.get(pb)) { d = 2; }           // nothing comes from there
            else if (pb != b && self.bTaken.get(pb) != self.bFall.get(pb)) {
                if (cond) { d = self.edgeDecides(p, pb, self.predKind.get(pf + k), bi); } else { d = 1; }
            }
            if (d < 0) { all = false; }
            self.tDec.push(d);
        }
        moved: bool = false;
        needFt: bool = false;
        fallToTaken: bool = false;
        for k in 0..pc {
            d: long = self.tDec.get(k);
            if (d < 0 || d == 2) { continue; }
            if (self.predKind.get(pf + k) == E_FALL) {
                if (d == 1 && cond) { fallToTaken = true; }
                continue;
            }
            pb: long = self.predBlock.get(pf + k);
            to: Sym = bi.name;
            if (d == 0) {
                to = fallLabel;
                if (to == NO_SYM) {
                    if (!all) { continue; }
                    needFt = true;
                    continue;
                }
            }
            self.retarget(p, pb, to);
            moved = true;
        }
        if (!all) { return moved; }
        // Every edge decided: the block's own branch goes. A fallthrough edge to the taken target
        // takes the slot before it as its jump; without one (no label, so the fallthrough is the
        // only edge) the branch's own slot is that jump.
        ft: Sym = NO_SYM;
        if (needFt) {
            self.threadSeq = self.threadSeq + 1;
            ft = internString(format(".TJ{}", self.threadSeq));
        }
        slot: long = self.first + br;
        if (fallToTaken) {
            if (br == self.bStart.get(b)) {
                if (needFt) { return moved; }   // cannot happen: a jump into it needs a label
                jm: Instr = instr(IROp.Jmp);
                jm.name = bi.name;
                p.code.set(slot, jm);
                self.nThreads = self.nThreads + 1;
                return true;
            }
            jm: Instr = instr(IROp.Jmp);
            jm.name = bi.name;
            p.code.set(slot - 1, jm);
        }
        if (needFt) {
            lb: Instr = instr(IROp.Label);
            lb.name = ft;
            p.code.set(slot, lb);
            for k in 0..pc {
                if (self.tDec.get(k) == 0 && self.predKind.get(pf + k) == E_TAKEN) {
                    self.retarget(p, self.predBlock.get(pf + k), ft);
                }
            }
        } else {
            p.code.set(slot, instr(IROp.Nop));
        }
        self.nThreads = self.nThreads + 1;
        // The branch was its temps' reader; constants nothing else reads go now, so a block that
        // held one before its jump (`b = const 0` falling into the branch) is a pass-through
        // block for the next round.
        self.dropDeadConsts(p, bi.a);
        if (!bi.bIsImm) { self.dropDeadConsts(p, bi.b); }
        return true;
    }

    // Every definition of `t`, when each is a `Const` and nothing reads `t`.
    dropDeadConsts &self inout p:IRProgram t:Temp -> void {
        if (self.rel(t) < 0) { return; }
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            if (in.op == IROp.Nop) { continue; }
            if (in.dst == t && in.op != IROp.Const) { return; }
            if (in.a == t || (!in.bIsImm && in.b == t)) { return; }
            for k in 0..in.argCount { if (p.args.get(in.firstArg + k) == t) { return; } }
            for k in 0..in.pieceCount { if (p.asmVals.get(in.firstPiece + k) == t) { return; } }
        }
        for i in 0..self.n {
            if (p.code.get(self.first + i).dst == t) {
                p.code.set(self.first + i, instr(IROp.Nop));
                self.nDead = self.nDead + 1;
            }
        }
    }

    // Point the branch that ends block `pb` at `to`, or at where `to` itself only jumps on to.
    retarget &self inout p:IRProgram pb:long to:Sym -> void {
        at: long = self.first + self.lastReal(p, pb);
        in: Instr = p.code.get(at);
        in.name = self.forward(p, to);
        p.code.set(at, in);
        self.nThreads = self.nThreads + 1;
    }

    // Where a jump to `name` ends up: through blocks of nothing but a `jmp` (or only a label,
    // falling into a labelled block), as they stand now, a few steps at most. A chain of them
    // collapses in one round rather than one round per link.
    forward &self inout p:IRProgram name:Sym -> Sym {
        n: Sym = name;
        steps: long = 0;
        while (steps < 8) {
            steps = steps + 1;
            hit: Option<long> = self.labelAt.find(n as long);
            b: long = -1;
            match hit { Some(x) { b = x; } None { return n; } }
            last: long = self.lastReal(p, b);
            if (last < 0) { return n; }
            for i in self.bStart.get(b)..last {
                o: IROp = p.code.get(self.first + i).op;
                if (o != IROp.Label && o != IROp.Nop) { return n; }
            }
            li: Instr = p.code.get(self.first + last);
            if (li.op == IROp.Jmp) {
                if (li.name == n) { return n; }
                n = li.name;
            } else if (li.op == IROp.Label) {
                fb: long = self.bFall.get(b);
                if (fb < 0 || fb == b) { return n; }
                nl: Sym = self.labelOf(p, fb);
                if (nl == NO_SYM) { return n; }
                n = nl;
            } else { return n; }
        }
        return n;
    }

    // Whether block `b` is labels, then a `jmp`: nothing a jump into it needs to stop for.
    jumpOnly &self inout p:IRProgram b:long -> bool {
        for i in self.bStart.get(b)..self.stopOf(b) {
            o: IROp = p.code.get(self.first + i).op;
            if (o == IROp.Jmp) { return true; }
            if (o != IROp.Label && o != IROp.Nop) { return false; }
        }
        return false;
    }

    // The label a block starts with, or NO_SYM.
    labelOf &self inout p:IRProgram b:long -> Sym {
        for i in self.bStart.get(b)..self.stopOf(b) {
            in: Instr = p.code.get(self.first + i);
            if (in.op == IROp.Label) { return in.name; }
            if (in.op != IROp.Nop) { return NO_SYM; }
        }
        return NO_SYM;
    }

    // Whether the edge from `pb` (taken or fallthrough) decides the conditional branch `bi`:
    // 1 taken, 0 not, -1 unknown.
    edgeDecides &self inout p:IRProgram pb:long kind:long bi:Instr -> long {
        op: IROp = IROp.CmpEq;
        uns: bool = false;
        isImm: bool = true;
        imm: long = 0;
        if (bi.op == IROp.Jcc) {
            op = bi.cmpOp;
            uns = kindUnsigned(bi.kind);
            isImm = bi.bIsImm;
            imm = bi.bImm;
            if (!isImm && self.singleConst(p, bi.b)) { isImm = true; imm = self.cv; }
        }
        // The tested values, as the edge's own definitions leave them.
        if (self.constOnEdge(p, pb, bi.a)) {
            x: long = self.cv;
            y: long = imm;
            if (!isImm) {
                if (!self.constOnEdge(p, pb, bi.b)) { return -1; }
                y = self.cv;
            }
            if (bi.op == IROp.Jz) { return boolWord(x == 0); }
            return boolWord(compareHolds(op, canon(bi.kind, x), canon(bi.kind, y), uns));
        }
        // The predecessor's own branch on the same operands, by the edge it takes.
        last: long = self.lastReal(p, pb);
        if (last < 0) { return -1; }
        pi: Instr = p.code.get(self.first + last);
        if (pi.a != bi.a || !(pi.op == IROp.Jz || (pi.op == IROp.Jcc && !isFloatKind(pi.kind)))) { return -1; }
        if (pi.op != bi.op || pi.kind != bi.kind) { return -1; }
        fo: IROp = IROp.CmpEq;
        fImm: bool = true;
        fc: long = 0;
        if (pi.op == IROp.Jcc) {
            fo = pi.cmpOp;
            fImm = pi.bIsImm;
            fc = pi.bImm;
            if (!fImm && self.singleConst(p, pi.b)) { fImm = true; fc = self.cv; }
            if (!fImm && (isImm || pi.b != bi.b)) { return -1; }
            if (fImm && !isImm) { return -1; }
        }
        if (kind == E_FALL) { fo = negateCompare(fo); }
        if (fImm && fo == IROp.CmpEq) { return boolWord(compareHolds(op, fc, imm, uns)); }
        if (fImm && fc != imm) { return -1; }
        if (implies(fo, op)) { return 1; }
        if (implies(fo, negateCompare(op))) { return 0; }
        return -1;
    }

    // Whether `t` holds a known constant at the end of block `pb`: its last definition there, or
    // in the chain of single predecessors leading to it, is a `Const`, or it has one definition
    // anywhere and that is a constant. The value is left in `cv`.
    constOnEdge &self inout p:IRProgram pb:long t:Temp -> bool {
        if (self.singleConst(p, t)) { return true; }
        if (self.rel(t) < 0) { return false; }
        // Which temps some `Const` writes, worked out the first time it is asked: only those can
        // be a constant on an edge.
        if (!self.tConstReady) {
            self.tConstReady = true;
            fillBool(&self.tConst, self.nt, false);
            for i in 0..self.n {
                in: Instr = p.code.get(self.first + i);
                r: long = self.rel(in.dst);
                if (in.op == IROp.Const && r >= 0) { self.tConst.set(r, true); }
            }
        }
        if (!self.tConst.get(self.rel(t))) { return false; }
        b: long = pb;
        steps: long = 0;
        while (steps < 8) {
            steps = steps + 1;
            i: long = self.bEnd.get(b);
            s: long = self.bStart.get(b);
            while (i >= s) {
                in: Instr = p.code.get(self.first + i);
                if (in.op != IROp.Nop && in.dst == t) {
                    if (in.op != IROp.Const) { return false; }
                    self.cv = in.imm;
                    return true;
                }
                i = i - 1;
            }
            if (b == 0 || self.predCount.get(b) != 1) { return false; }
            b = self.predBlock.get(self.predFirst.get(b));
        }
        return false;
    }

    // ─── addresses that are constants, and slots that escape ─────────────────

    // Which temps hold `&slot + k` wherever they hold anything, and which slots' addresses reach
    // something other than a load, a store or a block copy through them. A slot whose address
    // never escapes can be written only by name or through those temps, so no other pointer, and
    // no callee, reaches it.
    addressConstants &self inout p:IRProgram -> void {
        fillLong(&self.acRoot, self.nt, -1);
        fillLong(&self.acKind, self.nt, R_TEMP);
        fillLong(&self.acOff, self.nt, 0);
        if (self.exposed.cap() > 512) { self.exposed = map![]; } else { self.exposed.clear(); }
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            r: long = self.rel(in.dst);
            if (r < 0 || self.defs.get(r) != 1) { continue; }
            if (in.op == IROp.AddrOf && in.name != NO_SYM) {
                self.acRoot.set(r, in.name as long);
                if (in.isGlobal) { self.acKind.set(r, R_GLOBAL); } else { self.acKind.set(r, R_SLOT); }
                continue;
            }
            // A hidden scratch slot is a frame slot like a named one, numbered past every name.
            if (in.op == IROp.AggSlot) {
                self.acRoot.set(r, AGG_BASE + in.imm);
                self.acKind.set(r, R_SLOT);
                continue;
            }
            ar: long = self.rel(in.a);
            if (ar < 0 || self.acRoot.get(ar) < 0) { continue; }
            k: long = 0;
            if (in.op == IROp.Add) {
                if (!self.bConst(p, in, 0)) { continue; }
                k = self.cv;
            } else if (in.op != IROp.Mov) { continue; }
            self.acRoot.set(r, self.acRoot.get(ar));
            self.acKind.set(r, self.acKind.get(ar));
            self.acOff.set(r, self.acOff.get(ar) + k);
        }
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            o: IROp = in.op;
            if (o == IROp.Nop || o == IROp.Label) { continue; }
            if (o == IROp.AddrOf) {
                if (in.name != NO_SYM && self.acOf(in.dst) < 0) { self.exposed.put(in.name as long, true); }
                continue;
            }
            if (o == IROp.AggSlot) {
                if (self.acOf(in.dst) < 0) { self.exposed.put(AGG_BASE + in.imm, true); }
                continue;
            }
            if (o == IROp.Asm) {
                for k in 0..in.pieceCount {
                    nm: Sym = p.asmNames.get(in.firstPiece + k);
                    if (nm != NO_SYM) { self.exposed.put(nm as long, true); }
                }
            }
            if (o == IROp.PtrLoad || o == IROp.AggZero) { continue; }
            if (o == IROp.AggCopy) { continue; }
            if (o == IROp.PtrStore) { self.expose(in.b); continue; }
            if ((o == IROp.Add || o == IROp.Mov) && self.acOf(in.dst) >= 0) { continue; }
            self.expose(in.a);
            if (!in.bIsImm) { self.expose(in.b); }
            for k in 0..in.argCount { self.expose(p.args.get(in.firstArg + k)); }
            for k in 0..in.pieceCount { self.expose(p.asmVals.get(in.firstPiece + k)); }
        }
    }

    acOf &self t:Temp -> long {
        r: long = self.rel(t);
        if (r < 0) { return -1; }
        return self.acRoot.get(r);
    }

    expose &self t:Temp -> void {
        r: long = self.rel(t);
        if (r < 0 || self.acRoot.get(r) < 0) { return; }
        self.exposed.put(self.acRoot.get(r), true);
    }

    // ─── the facts ───────────────────────────────────────────────────────────

    // Every fact the function can establish, the location each memory access names, and what
    // each store, call and definition ends. False when the function is too big to solve.
    collectFacts &self inout p:IRProgram -> bool {
        self.addressConstants(p);
        self.fKind.clear(); self.fOp.clear(); self.fA.clear(); self.fB.clear(); self.fImm.clear();
        self.fIsImm.clear(); self.fUns.clear(); self.fLoc.clear(); if (self.factKey.cap() > 512) { self.factKey = map![]; } else { self.factKey.clear(); }
        self.lRootKind.clear(); self.lRoot.clear(); self.lOff.clear(); self.lWidth.clear(); self.lCls.clear();
        if (self.locKey.cap() > 512) { self.locKey = map![]; } else { self.locKey.clear(); }
        if (self.rootKey.cap() > 512) { self.rootKey = map![]; } else { self.rootKey.clear(); } self.rRk.clear(); self.rRoot.clear(); self.rootHead.clear();
        self.locNext.clear(); self.locFactHead.clear(); self.factNext.clear();
        fillLong(&self.instLoc, self.n, -1);
        fillLong(&self.instFact, self.n, -1);
        self.copies.clear();
        self.needNonneg = false;
        nb: long = self.bStart.len();
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            if (!self.reach.get(self.blockOf.get(i))) { continue; }
            o: IROp = in.op;
            if (o == IROp.PtrLoad && in.dst != NO_TEMP && !isAggregate(in.kind)) {
                loc: long = self.locFor(in.a, in.imm, kindWidth(in.kind), loadClass(in.kind));
                self.instLoc.set(i, loc);
                // Not a global (see below), and not `p = [p + 8]`, whose location moved with it.
                if (self.lRootKind.get(loc) != R_GLOBAL && !(self.lRootKind.get(loc) == R_TEMP && self.lRoot.get(loc) == in.dst)) {
                    self.instFact.set(i, self.memFact(loc, in.dst));
                }
            } else if (o == IROp.PtrStore && in.a != NO_TEMP) {
                w: long = kindWidth(in.kind);
                loc: long = self.locFor(in.a, in.imm, w, loadClass(in.kind));
                self.instLoc.set(i, loc);
                if (self.lRootKind.get(loc) != R_GLOBAL && !in.bIsImm && in.b != NO_TEMP && forwardable(in.kind, p.kindOf(in.b))) {
                    self.instFact.set(i, self.memFact(loc, in.b));
                }
            } else if ((o == IROp.Load || o == IROp.Store) && in.name != NO_SYM) {
                rk: long = R_SLOT;
                if (in.isGlobal) { rk = R_GLOBAL; }
                loc: long = self.locAt(rk, in.name as long, 0, 8, 16);
                self.instLoc.set(i, loc);
                // A global's value is never carried from one read to the next: another thread may
                // write it between two plain reads, and a polling loop must see that.
                if (in.isGlobal) { }
                else if (o == IROp.Load && in.dst != NO_TEMP && !isAggregate(in.kind)) {
                    self.instFact.set(i, self.memFact(loc, in.dst));
                } else if (o == IROp.Store && in.a != NO_TEMP) { self.instFact.set(i, self.memFact(loc, in.a)); }
            } else if (o == IROp.Bounds && in.a != NO_TEMP && in.b != NO_TEMP) {
                bop: IROp = IROp.CmpLt;
                if (in.imm == 1) { bop = IROp.CmpLe; }
                self.instFact.set(i, self.relFact(p, bop, in.a, in.b, false, 0, true));
                self.needNonneg = true;
            } else if (o == IROp.AggCopy) {
                self.copies.push(i);
            } else if (o == IROp.Div || o == IROp.Mod) {
                self.needNonneg = true;
            }
        }
        // A branch's facts ride on its edges.
        for b in 0..nb {
            if (!self.reach.get(b)) { continue; }
            last: long = self.lastReal(p, b);
            if (last < 0) { continue; }
            in: Instr = p.code.get(self.first + last);
            if (in.op == IROp.Jcc && !isFloatKind(in.kind) && in.a != NO_TEMP) {
                if (in.bIsImm || self.singleConst(p, in.b)) { self.needNonneg = true; }
                uns: bool = kindUnsigned(in.kind);
                self.bCond.set(b, self.relFact(p, in.cmpOp, in.a, in.b, in.bIsImm, in.bImm, uns));
                self.bNeg.set(b, self.relFact(p, negateCompare(in.cmpOp), in.a, in.b, in.bIsImm, in.bImm, uns));
            } else if (in.op == IROp.Jz && in.a != NO_TEMP) {
                self.bCond.set(b, self.relFact(p, IROp.CmpEq, in.a, NO_TEMP, true, 0, false));
                self.bNeg.set(b, self.relFact(p, IROp.CmpNe, in.a, NO_TEMP, true, 0, false));
            }
        }
        self.exprFacts(p);
        self.mapCopies(p);
        self.nf = self.fKind.len();
        if (self.nf == 0) { return false; }
        self.words = (self.nf + 63) / 64;
        if (nb * self.words * 64 > MAX_FLOW_BITS) { return false; }
        self.indexFacts(p);
        return true;
    }

    // A block copy carries what is known about its source to its destination: a field stored into
    // a struct being built, copied into a local, reads back as the temp stored. For each copy,
    // each memory fact inside the source becomes a pair (source fact, the same value at the
    // destination), and the copy establishes the second wherever the first holds just before it.
    // Repeated, so a chain of copies (a callee's scratch, its result slot, the local) carries a
    // value through. A block holding such a copy is solved by walking it (`bDyn`).
    mapCopies &self inout p:IRProgram -> void {
        nc: long = self.copies.len();
        fillLong(&self.cmFirst, nc, 0);
        fillLong(&self.cmCount, nc, 0);
        self.cmSrc.clear();
        self.cmDst.clear();
        self.bDyn.clear();
        if (self.copyAt.cap() > 512) { self.copyAt = map![]; } else { self.copyAt.clear(); }
        for b in 0..self.bStart.len() { self.bDyn.push(false); }
        for c in 0..nc { self.copyAt.put(self.copies.get(c), c); }
        rounds: long = 0;
        going: bool = nc > 0;
        while (going && rounds < 4) {
            going = false;
            rounds = rounds + 1;
            for c in 0..nc {
                i: long = self.copies.get(c);
                in: Instr = p.code.get(self.first + i);
                if (in.op != IROp.AggCopy || in.a == NO_TEMP || in.b == NO_TEMP) { continue; }
                dr: long = self.rel(in.a);
                sr: long = self.rel(in.b);
                if (dr < 0 || sr < 0) { continue; }
                dk: long = R_TEMP;
                droot: long = in.a;
                doff: long = 0;
                if (self.acRoot.get(dr) >= 0) { dk = self.acKind.get(dr); droot = self.acRoot.get(dr); doff = self.acOff.get(dr); }
                sk: long = R_TEMP;
                sroot: long = in.b;
                soff: long = 0;
                if (self.acRoot.get(sr) >= 0) { sk = self.acKind.get(sr); sroot = self.acRoot.get(sr); soff = self.acOff.get(sr); }
                if (dk == R_GLOBAL || sk == R_GLOBAL || (dk == sk && droot == sroot)) { continue; }
                // This copy's pairs are rebuilt each round: the list of facts has grown. Only the
                // source's own locations are walked; what is added lands under the destination.
                first: long = self.cmSrc.len();
                rid: long = self.findRoot(sk, sroot);
                l: long = -1;
                if (rid >= 0) { l = self.rootHead.get(rid); }
                while (l >= 0) {
                    off: long = self.lOff.get(l);
                    if (off >= soff && off + self.lWidth.get(l) <= soff + in.imm) {
                        f: long = self.locFactHead.get(l);
                        while (f >= 0) {
                            l2: long = self.locAt(dk, droot, off - soff + doff, self.lWidth.get(l), self.lCls.get(l));
                            before: long = self.fKind.len();
                            f2: long = self.memFact(l2, self.fA.get(f));
                            if (self.fKind.len() > before) { going = true; }
                            self.cmSrc.push(f);
                            self.cmDst.push(f2);
                            f = self.factNext.get(f);
                        }
                    }
                    l = self.locNext.get(l);
                }
                self.cmFirst.set(c, first);
                self.cmCount.set(c, self.cmSrc.len() - first);
                if (self.cmSrc.len() > first) { self.bDyn.set(self.blockOf.get(i), true); }
            }
        }
        self.cmOn.clear();
        most: long = 0;
        for c in 0..nc { if (self.cmCount.get(c) > most) { most = self.cmCount.get(c); } }
        for k in 0..most { self.cmOn.push(false); }
    }

    // The location `[t + off]` names: relative to a slot when `t` is an address constant, to
    // `t` itself otherwise.
    locFor &self t:Temp off:long width:long cls:long -> long {
        r: long = self.rel(t);
        if (r >= 0 && self.acRoot.get(r) >= 0) {
            return self.locAt(self.acKind.get(r), self.acRoot.get(r), self.acOff.get(r) + off, width, cls);
        }
        return self.locAt(R_TEMP, t, off, width, cls);
    }

    locAt &self rk:long root:long off:long width:long cls:long -> long {
        key: long = mix(mix(mix(mix(rk, root), off), width), cls);
        old: long = self.findLoc(rk, root, off, width, cls);
        if (old >= 0) { return old; }
        self.lRootKind.push(rk);
        self.lRoot.push(root);
        self.lOff.push(off);
        self.lWidth.push(width);
        self.lCls.push(cls);
        l: long = self.lRootKind.len() - 1;
        if (!self.locKey.has(key)) { self.locKey.put(key, l); }
        rid: long = self.findRoot(rk, root);
        if (rid < 0) {
            rid = self.rRk.len();
            self.rRk.push(rk);
            self.rRoot.push(root);
            self.rootHead.push(-1);
            self.rootKey.put(mix(rk, root), rid);
        }
        self.locNext.push(self.rootHead.get(rid));
        self.rootHead.set(rid, l);
        self.locFactHead.push(-1);
        return l;
    }

    // The locations relative to one root are a list, newest first, from `rootHead`.
    findRoot &self rk:long root:long -> long {
        hit: Option<long> = self.rootKey.find(mix(rk, root));
        match hit {
            Some(r) { if (self.rRk.get(r) == rk && self.rRoot.get(r) == root) { return r; } }
            None { }
        }
        // A collision: the slow way, which is rare enough not to matter.
        for r in 0..self.rRk.len() { if (self.rRk.get(r) == rk && self.rRoot.get(r) == root) { return r; } }
        return -1;
    }

    // A location already in the table, or -1.
    findLoc &self rk:long root:long off:long width:long cls:long -> long {
        key: long = mix(mix(mix(mix(rk, root), off), width), cls);
        hit: Option<long> = self.locKey.find(key);
        match hit {
            Some(old) {
                if (self.lRootKind.get(old) == rk && self.lRoot.get(old) == root && self.lOff.get(old) == off
                    && self.lWidth.get(old) == width && self.lCls.get(old) == cls) { return old; }
            }
            None { }
        }
        return -1;
    }

    memFact &self loc:long v:Temp -> long {
        return self.addFact(F_MEM, IROp.CmpEq, v, NO_TEMP, 0, false, false, loc);
    }

    // A relation, with an operand that is a constant temp folded into an immediate, so the fact
    // ends only when the other operand is written.
    relFact &self inout p:IRProgram op:IROp a:Temp b:Temp isImm:bool imm:long uns:bool -> long {
        if (!isImm && b != NO_TEMP && self.singleConst(p, b)) { isImm = true; imm = self.cv; b = NO_TEMP; }
        if (isImm) { b = NO_TEMP; }
        return self.addFact(F_REL, op, a, b, imm, isImm, uns, -1);
    }

    addFact &self kind:long op:IROp a:Temp b:Temp imm:long isImm:bool uns:bool loc:long -> long {
        u: long = 0;
        if (uns) { u = 1; }
        ii: long = 0;
        if (isImm) { ii = 1; }
        key: long = mix(mix(mix(mix(mix(mix(kind, op as long), a), b), imm), ii * 2 + u), loc);
        hit: Option<long> = self.factKey.find(key);
        match hit {
            Some(old) {
                if (self.fKind.get(old) == kind && self.fOp.get(old) == op && self.fA.get(old) == a && self.fB.get(old) == b
                    && self.fImm.get(old) == imm && self.fIsImm.get(old) == isImm && self.fUns.get(old) == uns
                    && self.fLoc.get(old) == loc) { return old; }
            }
            None { }
        }
        self.fKind.push(kind);
        self.fOp.push(op);
        self.fA.push(a);
        self.fB.push(b);
        self.fImm.push(imm);
        self.fIsImm.push(isImm);
        self.fUns.push(uns);
        self.fLoc.push(loc);
        f: long = self.fKind.len() - 1;
        if (!self.factKey.has(key)) { self.factKey.put(key, f); }
        if (kind == F_MEM) {
            self.factNext.push(self.locFactHead.get(loc));
            self.locFactHead.set(loc, f);
        } else {
            self.factNext.push(-1);
        }
        return f;
    }

    // What the dataflow looks up, built once the facts are all known: the facts that name each
    // temp (a definition of it ends them), and three sets of memory facts.
    indexFacts &self inout p:IRProgram -> void {
        nf: long = self.nf;
        fillLong(&self.tfCount, self.nt, 0);
        for f in 0..nf { self.forTemps(f, 0); }
        self.tfFirst.clear();
        total: long = 0;
        for r in 0..self.nt { self.tfFirst.push(total); total = total + self.tfCount.get(r); }
        fillLong(&self.tfList, total, 0);
        fillLong(&self.tfCount, self.nt, 0);
        for f in 0..nf { self.forTemps(f, 1); }

        // What a call ends (memory through a pointer, globals, and slots whose address escaped),
        // what `asm` ends (all of it), and what a pointer may reach that a named store can (memory
        // through a pointer). A store's own kill is built from these and its root's list, so it
        // costs a pass over words, not over every fact.
        fillLong(&self.callKill, self.words, 0);
        fillLong(&self.allMem, self.words, 0);
        fillLong(&self.tempMem, self.words, 0);
        for f in 0..nf {
            if (self.fKind.get(f) != F_MEM) { continue; }
            setBit(&self.allMem, 0, f);
            l: long = self.fLoc.get(f);
            rk: long = self.lRootKind.get(l);
            if (rk != R_SLOT || self.exposed.has(self.lRoot.get(l))) { setBit(&self.callKill, 0, f); }
            if (rk == R_TEMP) { setBit(&self.tempMem, 0, f); }
        }
    }

    // The memory facts a write of `width` bytes at (rk, root, off) ends, as `mayAlias` says,
    // cleared from (mode 0) or added to (mode 1) the set at `at`.
    killRegion &self at:long mode:long rk:long root:long off:long width:long -> void {
        rid: long = self.findRoot(rk, root);
        if (rk == R_TEMP) {
            // Everything a pointer reaches, except what lies beside the written bytes under the
            // same pointer: those are set aside first and put back as they were.
            self.keep.clear();
            l: long = -1;
            if (rid >= 0) { l = self.rootHead.get(rid); }
            while (l >= 0) {
                lo: long = self.lOff.get(l);
                if (!(off < lo + self.lWidth.get(l) && lo < off + width)) {
                    f: long = self.locFactHead.get(l);
                    while (f >= 0) {
                        if (self.has(at, f) == (mode == 0)) { self.keep.push(f); }
                        f = self.factNext.get(f);
                    }
                }
                l = self.locNext.get(l);
            }
            self.touchSet(at, 0, mode);
            for k in 0..self.keep.len() { self.touch(at, self.keep.get(k), 1 - mode); }
            return;
        }
        l: long = -1;
        if (rid >= 0) { l = self.rootHead.get(rid); }
        while (l >= 0) {
            lo: long = self.lOff.get(l);
            if (off < lo + self.lWidth.get(l) && lo < off + width) {
                f: long = self.locFactHead.get(l);
                while (f >= 0) { self.touch(at, f, mode); f = self.factNext.get(f); }
            }
            l = self.locNext.get(l);
        }
        if (rk == R_GLOBAL || self.exposed.has(root)) { self.touchSet(at, 2, mode); }
    }

    // Count (mode 0) or list (mode 1) fact `f` under every temp it names.
    forTemps &self f:long mode:long -> void {
        if (self.fKind.get(f) == F_REL) {
            self.noteTemp(self.fA.get(f), f, mode);
            if (!self.fIsImm.get(f)) { self.noteTemp(self.fB.get(f), f, mode); }
        } else if (self.fKind.get(f) == F_EXPR) {
            // The temp holding the value, and the expression's operands.
            self.noteTemp(self.fA.get(f), f, mode);
            g: long = self.fLoc.get(f);
            self.noteTemp(self.eA.get(g), f, mode);
            if (self.eB.get(g) != NO_TEMP && self.eB.get(g) != self.eA.get(g)) { self.noteTemp(self.eB.get(g), f, mode); }
        } else {
            self.noteTemp(self.fA.get(f), f, mode);
            l: long = self.fLoc.get(f);
            if (self.lRootKind.get(l) == R_TEMP && self.lRoot.get(l) != self.fA.get(f)) { self.noteTemp(self.lRoot.get(l), f, mode); }
        }
    }

    // ─── common subexpressions ───────────────────────────────────────────────

    // "Temp t holds `a op b`" is a fact like the others: the instruction computing it into t
    // establishes it, and a definition of t, a or b ends it (`forTemps` lists it under all three),
    // so where it holds on entry from every path, a second computation of the same expression is
    // a copy of t (`reuseExpr`). An expression is the operation, its operands (or immediate), its
    // type and a conversion's two types: computed again from the same temps it is the same value,
    // whatever the operation (a division that could fault already ran, on every path here). Facts
    // are made only for expressions that occur more than once, counted with the operands seen
    // through the expressions that define them (`shape`), so `p + i * 8` written twice is found
    // even when its `i * 8` was computed into two temps: the inner one becomes a copy first, and
    // the outer one's operands are then read through the copy (`resolve`).
    exprFacts &self inout p:IRProgram -> void {
        fillLong(&self.instExpr, self.n, -1);
        if (gCseOff) { return; }
        fillLong(&self.shapeOf, self.nt, 0);
        self.eOp.clear(); self.eA.clear(); self.eB.clear(); self.eImm.clear(); self.eIsImm.clear();
        self.eKind.clear(); self.eFrom.clear(); self.eTo.clear(); self.eHead.clear();
        if (self.eKey.cap() > 512) { self.eKey = map![]; } else { self.eKey.clear(); }
        if (self.shapeCount.cap() > 512) { self.shapeCount = map![]; } else { self.shapeCount.clear(); }
        any: bool = false;
        for i in 0..self.n {
            if (p.code[self.first + i].dst == NO_TEMP) { continue; }
            in: Instr = p.code.get(self.first + i);
            if (!self.reach.get(self.blockOf.get(i))) { continue; }
            if (!self.cseCandidate(in)) {
                // What a single definition reads, for the shapes of what is computed from it.
                r: long = self.rel(in.dst);
                if (r < 0 || self.defs.get(r) != 1) { continue; }
                o: IROp = in.op;
                s0: long = 0;
                if (o == IROp.PtrLoad) { s0 = mix(mix(mix(o as long, self.operandShape(in.a)), in.imm), in.kind as long); }
                else if (o == IROp.Load || o == IROp.AddrOf) { s0 = mix(mix(o as long, in.name as long), boolWord(in.isGlobal)); }
                else if (o == IROp.AggSlot || o == IROp.Const) { s0 = mix(mix(o as long, in.imm), in.kind as long); }
                else if (o == IROp.Mov) { s0 = self.operandShape(in.a); }
                self.shapeOf.set(r, s0);
                continue;
            }
            s: long = self.shape(in);
            r: long = self.rel(in.dst);
            if (self.defs.get(r) == 1) { self.shapeOf.set(r, s); }
            hit: Option<long> = self.shapeCount.find(s);
            c: long = 0;
            match hit { Some(k) { c = k; any = true; } None { } }
            self.shapeCount.put(s, c + 1);
        }
        if (!any) { return; }
        for i in 0..self.n {
            if (p.code[self.first + i].dst == NO_TEMP) { continue; }
            in: Instr = p.code.get(self.first + i);
            if (!self.cseCandidate(in) || !self.reach.get(self.blockOf.get(i))) { continue; }
            hit: Option<long> = self.shapeCount.find(self.shape(in));
            match hit { Some(k) { if (k < 2) { continue; } } None { continue; } }
            g: long = self.exprGroup(in, true);
            if (g < 0) { continue; }
            before: long = self.fKind.len();
            f: long = self.addFact(F_EXPR, in.op, in.dst, NO_TEMP, 0, false, false, g);
            if (self.fKind.len() > before) {
                while (self.eNext.len() <= f) { self.eNext.push(-1); }
                self.eNext.set(f, self.eHead.get(g));
                self.eHead.set(g, f);
            }
            self.instFact.set(i, f);
            self.instExpr.set(i, g);
        }
    }

    // An instruction whose whole effect is its destination's value, computed from its operands
    // alone, into a temp that is not one of them.
    cseCandidate &self in:Instr -> bool {
        o: IROp = in.op;
        if (!(isArith(o) || isCompare(o) || o == IROp.Convert || o == IROp.BNot)) { return false; }
        if (in.dst == NO_TEMP || in.a == NO_TEMP || in.dst == in.a || self.rel(in.dst) < 0) { return false; }
        if (o == IROp.Convert || o == IROp.BNot) { return true; }
        if (in.bIsImm) { return true; }
        return in.b != NO_TEMP && in.b != in.dst;
    }

    // The expression's structure, its operands seen through the single definitions that made
    // them: only ever compared for counting, never trusted as an equality of values.
    shape &self in:Instr -> long {
        h: long = mix(mix(mix(in.op as long, in.kind as long), in.fromKind as long), in.toKind as long);
        h = mix(h, self.operandShape(in.a));
        if (in.bIsImm) { h = mix(mix(h, 1), in.bImm); }
        else if (in.op != IROp.Convert && in.op != IROp.BNot) { h = mix(h, self.operandShape(in.b)); }
        return h;
    }

    operandShape &self t:Temp -> long {
        r: long = self.rel(t);
        if (r >= 0 && self.shapeOf.get(r) != 0) { return self.shapeOf.get(r); }
        return mix(t, 7);
    }

    // The group of facts for this exact expression (its operands as written), made when `make`
    // says so; -1 when there is none (or a hash collision, which is simply not reused).
    exprGroup &self in:Instr make:bool -> long {
        return self.exprGroupOf(in.op, in.a, in.b, in.bIsImm, in.bImm, in.kind, in.fromKind, in.toKind, make);
    }

    exprGroupOf &self o:IROp a:Temp b0:Temp isImm:bool imm:long k:Lit fk:Lit tk:Lit make:bool -> long {
        b: Temp = b0;
        if (isImm || o == IROp.Convert || o == IROp.BNot) { b = NO_TEMP; }
        if (!isImm) { imm = 0; }
        key: long = mix(mix(mix(mix(mix(mix(mix(o as long, a), b), imm), boolWord(isImm)), k as long), fk as long), tk as long);
        hit: Option<long> = self.eKey.find(key);
        match hit {
            Some(g) {
                if (self.eOp.get(g) == o && self.eA.get(g) == a && self.eB.get(g) == b && self.eImm.get(g) == imm
                    && self.eIsImm.get(g) == isImm && self.eKind.get(g) == k && self.eFrom.get(g) == fk && self.eTo.get(g) == tk) { return g; }
                return -1;
            }
            None { }
        }
        if (!make) { return -1; }
        g: long = self.eOp.len();
        self.eOp.push(o); self.eA.push(a); self.eB.push(b); self.eImm.push(imm); self.eIsImm.push(isImm);
        self.eKind.push(k); self.eFrom.push(fk); self.eTo.push(tk); self.eHead.push(-1);
        self.eKey.put(key, g);
        return g;
    }

    // `dst = a op b` where some temp already holds `a op b` here: a copy of it. The operands are
    // read through the copies seen in this block, so an expression over a value just found again
    // is found too.
    reuseExpr &self inout p:IRProgram ix:long i:long in:Instr at:long -> bool {
        g: long = self.instExpr.get(i);
        ra: Temp = self.resolve(in.a);
        rb: Temp = in.b;
        if (!in.bIsImm && in.op != IROp.Convert && in.op != IROp.BNot) { rb = self.resolve(in.b); }
        if (ra != in.a || rb != in.b) {
            g2: long = self.exprGroupOf(in.op, ra, rb, in.bIsImm, in.bImm, in.kind, in.fromKind, in.toKind, false);
            if (g2 >= 0) { g = g2; }
        }
        if (g < 0) { return false; }
        f: long = self.eHead.get(g);
        while (f >= 0) {
            if (self.has(at, f) && self.fA.get(f) != in.dst) {
                mv: Instr = instr(IROp.Mov);
                mv.dst = in.dst;
                mv.a = self.fA.get(f);
                mv.kind = in.kind;
                if (in.op == IROp.Convert) { mv.kind = in.toKind; }
                mv.structName = in.structName;
                p.code.set(ix, mv);
                self.nCse = self.nCse + 1;
                self.nMovs = self.nMovs + 1;
                return true;
            }
            f = self.eNext.get(f);
        }
        return false;
    }

    noteTemp &self t:Temp f:long mode:long -> void {
        r: long = self.rel(t);
        if (r < 0) { return; }
        if (mode == 1) { self.tfList.set(self.tfFirst.get(r) + self.tfCount.get(r), f); }
        self.tfCount.set(r, self.tfCount.get(r) + 1);
    }

    // May a write of `width` bytes at (rk, root, off) change location `l`?
    mayAlias &self rk:long root:long off:long width:long l:long -> bool {
        lk: long = self.lRootKind.get(l);
        lr: long = self.lRoot.get(l);
        if (rk == lk && root == lr) {
            lo: long = self.lOff.get(l);
            return off < lo + self.lWidth.get(l) && lo < off + width;
        }
        if (rk == R_TEMP) {
            // Through a pointer: any other pointer's target, any global, any slot that escaped.
            if (lk == R_SLOT) { return self.exposed.has(lr); }
            return true;
        }
        // By name: only what a pointer may also reach, and only if this name can be reached so.
        if (lk == R_TEMP) { return rk == R_GLOBAL || self.exposed.has(root); }
        return false;
    }

    // ─── solving ─────────────────────────────────────────────────────────────

    setAt &self b:long which:long -> long { return (b * 4 + which) * self.words; }

    // What instruction `i` ends: clear those bits from the set at `at` (mode 0), or add them to
    // it (mode 1, building a block's kill set).
    killInstr &self inout p:IRProgram i:long at:long mode:long -> void {
        // The two fields nearly every instruction needs are read in place: this runs four times
        // per instruction, and a whole `Instr` copied out each time was most of its cost.
        ix: long = self.first + i;
        o: IROp = p.code[ix].op;
        r: long = self.rel(p.code[ix].dst);
        if (r >= 0) {
            s: long = self.tfFirst.get(r);
            for k in 0..self.tfCount.get(r) { self.touch(at, self.tfList.get(s + k), mode); }
        }
        if (o == IROp.Call || o == IROp.CallIndirect) { self.touchSet(at, 0, mode); return; }
        if (o == IROp.Asm) { self.touchSet(at, 1, mode); return; }
        if (o == IROp.PtrStore || o == IROp.Store) {
            l: long = self.instLoc.get(i);
            if (l >= 0) { self.killRegion(at, mode, self.lRootKind.get(l), self.lRoot.get(l), self.lOff.get(l), self.lWidth.get(l)); }
            return;
        }
        if (o != IROp.AggCopy && o != IROp.AggZero && o != IROp.ArrStore) { return; }
        in: Instr = p.code.get(ix);
        if (o == IROp.AggCopy || o == IROp.AggZero) {
            r: long = self.rel(in.a);
            if (r >= 0 && self.acRoot.get(r) >= 0) {
                self.killRegion(at, mode, self.acKind.get(r), self.acRoot.get(r), self.acOff.get(r), in.imm);
            } else {
                self.killRegion(at, mode, R_TEMP, in.a, 0, in.imm);
            }
            return;
        }
        if (o == IROp.ArrStore && in.name != NO_SYM) {
            rk: long = R_SLOT;
            if (in.isGlobal) { rk = R_GLOBAL; }
            self.killRegion(at, mode, rk, in.name as long, 0, LONG_MAX / 4);     // the whole array
        }
    }

    touch &self at:long f:long mode:long -> void {
        w: long = at + f / 64;
        m: long = 1 << (f % 64);
        if (mode == 0) { self.bits.set(w, self.bits.get(w) & ~m); }
        else { self.bits.set(w, self.bits.get(w) | m); }
    }

    // The same for a whole set: what a call ends (0), what `asm` ends (1), what a pointer reaches (2).
    touchSet &self at:long which:long mode:long -> void {
        for w in 0..self.words {
            s: long = self.callKill.get(w);
            if (which == 1) { s = self.allMem.get(w); }
            else if (which == 2) { s = self.tempMem.get(w); }
            if (mode == 0) { self.bits.set(at + w, self.bits.get(at + w) & ~s); }
            else { self.bits.set(at + w, self.bits.get(at + w) | s); }
        }
    }

    has &self at:long f:long -> bool {
        return (self.bits.get(at + f / 64) & (1 << (f % 64))) != 0;
    }

    solve &self inout p:IRProgram -> void {
        nb: long = self.bStart.len();
        W: long = self.words;
        fillLong(&self.bits, (nb * 4 + 1) * W, 0);
        scratch: long = nb * 4 * W;     // one more set, for the meet
        // Each block's own effect: what it ends, and what it establishes that survives to its end.
        for b in 0..nb {
            if (!self.reach.get(b)) { continue; }
            g: long = self.setAt(b, SET_GEN);
            k: long = self.setAt(b, SET_KILL);
            for i in self.bStart.get(b)..self.stopOf(b) {
                self.killInstr(p, i, g, 0);
                self.killInstr(p, i, k, 1);
                f: long = self.instFact.get(i);
                if (f >= 0) { self.touch(g, f, 1); }
            }
            // Optimistic start: everything, except at the entry, where nothing is known.
            if (b != 0) {
                in0: long = self.setAt(b, SET_IN);
                for w in 0..W { self.bits.set(in0 + w, -1); }
            }
            self.transfer(p, b);
        }
        going: bool = true;
        while (going) {
            going = false;
            for oi in 1..self.order.len() {
                b: long = self.order.get(oi);
                if (b == 0) { continue; }
                for w in 0..W { self.bits.set(scratch + w, -1); }
                pf: long = self.predFirst.get(b);
                for k in 0..self.predCount.get(b) {
                    pb: long = self.predBlock.get(pf + k);
                    if (!self.reach.get(pb)) { continue; }
                    self.meetEdge(scratch, pb, self.predKind.get(pf + k));
                }
                in0: long = self.setAt(b, SET_IN);
                changed: bool = false;
                for w in 0..W {
                    v: long = self.bits.get(scratch + w);
                    if (self.bits.get(in0 + w) != v) { self.bits.set(in0 + w, v); changed = true; }
                }
                if (changed) { self.transfer(p, b); going = true; }
            }
        }
    }

    // OUT = (IN - KILL) + GEN.
    transfer &self inout p:IRProgram b:long -> void {
        in0: long = self.setAt(b, SET_IN);
        out: long = self.setAt(b, SET_OUT);
        if (self.bDyn.get(b)) {
            for w in 0..self.words { self.bits.set(out + w, self.bits.get(in0 + w)); }
            for i in self.bStart.get(b)..self.stopOf(b) { self.step(p, i, out); }
            return;
        }
        g: long = self.setAt(b, SET_GEN);
        k: long = self.setAt(b, SET_KILL);
        for w in 0..self.words {
            self.bits.set(out + w, (self.bits.get(in0 + w) & ~self.bits.get(k + w)) | self.bits.get(g + w));
        }
    }

    // Intersect what the edge from `pb` carries into the set at `at`: its block's OUT, plus the
    // fact the branch establishes on that edge.
    meetEdge &self at:long pb:long kind:long -> void {
        out: long = self.setAt(pb, SET_OUT);
        f: long = self.bCond.get(pb);
        if (kind == E_FALL) { f = self.bNeg.get(pb); }
        // A conditional branch whose two edges reach the same block says nothing there.
        if (self.bTaken.get(pb) == self.bFall.get(pb)) { f = -1; }
        fw: long = -1;
        fm: long = 0;
        if (f >= 0) { fw = f / 64; fm = 1 << (f % 64); }
        for w in 0..self.words {
            v: long = self.bits.get(out + w);
            if (w == fw) { v = v | fm; }
            self.bits.set(at + w, self.bits.get(at + w) & v);
        }
    }

    // Walk block `b` from its IN, calling back for each instruction before its effect applies.
    // `cur` (at `curAt`) holds the facts at that point.
    startWalk &self b:long -> long {
        W: long = self.words;
        at: long = self.bStart.len() * 4 * W;     // the scratch set
        in0: long = self.setAt(b, SET_IN);
        for w in 0..W { self.bits.set(at + w, self.bits.get(in0 + w)); }
        return at;
    }

    step &self inout p:IRProgram i:long at:long -> void {
        // A copy's pairs read the facts before it, of its source; its kill is of its destination.
        c: long = 0;
        s: long = 0;
        if (self.cmSrc.len() > 0) {
            hit: Option<long> = self.copyAt.find(i);
            match hit { Some(k) { c = self.cmCount.get(k); s = self.cmFirst.get(k); } None { } }
        }
        for k in 0..c { self.cmOn.set(k, self.has(at, self.cmSrc.get(s + k))); }
        self.killInstr(p, i, at, 0);
        f: long = self.instFact.get(i);
        if (f >= 0) { self.touch(at, f, 1); }
        for k in 0..c { if (self.cmOn.get(k)) { self.touch(at, self.cmDst.get(s + k), 1); } }
    }

    // ─── what is known about one temp ────────────────────────────────────────

    // The signed interval the facts at `at` (and the temp's own constancy and sign) put `t` in,
    // left in `lo`/`hi`.
    interval &self inout p:IRProgram t:Temp at:long -> void {
        self.lo = LONG_MIN;
        self.hi = LONG_MAX;
        if (self.singleConst(p, t)) { self.lo = self.cv; self.hi = self.cv; return; }
        r: long = self.rel(t);
        if (r < 0) { return; }
        if (self.nonneg.len() > r && self.nonneg.get(r)) { self.lo = 0; }
        s: long = self.tfFirst.get(r);
        for k in 0..self.tfCount.get(r) {
            f: long = self.tfList.get(s + k);
            if (self.fKind.get(f) != F_REL || !self.fIsImm.get(f) || self.fUns.get(f) || self.fA.get(f) != t) { continue; }
            if (!self.has(at, f)) { continue; }
            c: long = self.fImm.get(f);
            o: IROp = self.fOp.get(f);
            if (o == IROp.CmpLt) { if (c - 1 < self.hi && c > LONG_MIN) { self.hi = c - 1; } }
            else if (o == IROp.CmpLe) { if (c < self.hi) { self.hi = c; } }
            else if (o == IROp.CmpGt) { if (c + 1 > self.lo && c < LONG_MAX) { self.lo = c + 1; } }
            else if (o == IROp.CmpGe) { if (c > self.lo) { self.lo = c; } }
            else if (o == IROp.CmpEq) { if (c > self.lo) { self.lo = c; } if (c < self.hi) { self.hi = c; } }
        }
    }

    knownNonneg &self inout p:IRProgram t:Temp at:long -> bool {
        r: long = self.rel(t);
        if (r >= 0 && self.nonneg.len() > r && self.nonneg.get(r)) { return true; }
        self.interval(p, t, at);
        return self.lo >= 0;
    }

    // Whether `a op b` (or `a op #imm`) holds at the point whose facts are at `at`: 1 when it
    // must, 0 when it cannot, -1 when the facts do not say.
    decide &self inout p:IRProgram op:IROp a:Temp b:Temp isImm:bool imm:long uns:bool at:long -> long {
        if (!isImm && b != NO_TEMP && self.singleConst(p, b)) { isImm = true; imm = self.cv; }
        if (!isImm && self.singleConst(p, a)) {
            // `c op b` is `b op' c`.
            c: long = self.cv;
            a = b;
            op = swapCompare(op);
            isImm = true;
            imm = c;
        }
        if (a == NO_TEMP) { return -1; }
        if (isImm) { return self.decideImm(p, op, a, imm, uns, at); }
        if (a == b) {
            if (op == IROp.CmpEq || op == IROp.CmpLe || op == IROp.CmpGe) { return 1; }
            return 0;
        }
        r: long = self.rel(a);
        if (r >= 0) {
            s: long = self.tfFirst.get(r);
            for k in 0..self.tfCount.get(r) {
                f: long = self.tfList.get(s + k);
                if (self.fKind.get(f) != F_REL || self.fIsImm.get(f) || !self.has(at, f)) { continue; }
                fo: IROp = self.fOp.get(f);
                if (self.fA.get(f) == a && self.fB.get(f) == b) { }
                else if (self.fA.get(f) == b && self.fB.get(f) == a) { fo = swapCompare(fo); }
                else { continue; }
                if (!self.signsAgree(p, fo, self.fUns.get(f), uns, a, b, at)) { continue; }
                if (implies(fo, op)) { return 1; }
                if (implies(fo, negateCompare(op))) { return 0; }
            }
            if (self.transDepth == 0 && op != IROp.CmpEq && op != IROp.CmpNe) {
                if (self.through(p, op, a, b, uns, at) == 1) { return 1; }
            }
        }
        // Two intervals that do not overlap, or meet only at the edge.
        if (uns) { return -1; }
        self.interval(p, a, at);
        alo: long = self.lo;
        ahi: long = self.hi;
        self.interval(p, b, at);
        return orderIntervals(op, alo, ahi, self.lo, self.hi);
    }

    // `a op b` (an order) through a third value: a fact `a < c` or `a <= c`, and then `c <= b` or
    // `c < b` as far as everything else known says (the facts, the intervals, but not a third
    // step). `i < mid` with `mid <= len` is `i < len`. Read in the fact's signedness; a question
    // asked unsigned is answered by a signed chain only when `a` is never negative (then b, above
    // it, is not either, and the two orders agree). Only ever says "holds" (1) or nothing (-1).
    through &self inout p:IRProgram op0:IROp a0:Temp b0:Temp uns:bool at:long -> long {
        op: IROp = op0;
        a: Temp = a0;
        b: Temp = b0;
        if (op == IROp.CmpGt || op == IROp.CmpGe) { op = swapCompare(op); a = b0; b = a0; }
        r: long = self.rel(a);
        if (r < 0) { return -1; }
        s: long = self.tfFirst.get(r);
        for k in 0..self.tfCount.get(r) {
            f: long = self.tfList.get(s + k);
            if (self.fKind.get(f) != F_REL || self.fIsImm.get(f) || !self.has(at, f)) { continue; }
            fo: IROp = self.fOp.get(f);
            c: Temp = self.fB.get(f);
            if (self.fA.get(f) == a) { }
            else if (self.fB.get(f) == a) { fo = swapCompare(fo); c = self.fA.get(f); }
            else { continue; }
            if ((fo != IROp.CmpLt && fo != IROp.CmpLe) || c == b || c == NO_TEMP) { continue; }
            fu: bool = self.fUns.get(f);
            if (fu != uns && !(uns && !fu && self.knownNonneg(p, a, at))) { continue; }
            need: IROp = IROp.CmpLe;
            if (fo == IROp.CmpLe && op == IROp.CmpLt) { need = IROp.CmpLt; }
            self.transDepth = 1;
            d: long = self.decide(p, need, c, b, false, 0, fu, at);
            self.transDepth = 0;
            if (d == 1) { return 1; }
        }
        return -1;
    }

    // A fact about `a fo b` read with one signedness answers a question asked with the other only
    // where the two orders agree: when both operands are never negative. An equality is the same
    // in both.
    signsAgree &self inout p:IRProgram fo:IROp factUns:bool uns:bool a:Temp b:Temp at:long -> bool {
        if (factUns == uns || fo == IROp.CmpEq || fo == IROp.CmpNe) { return true; }
        // a < b or a <= b with a >= 0 puts both at or above zero; a > b, a >= b with b >= 0 too.
        if (!factUns) {
            if (fo == IROp.CmpLt || fo == IROp.CmpLe) { return self.knownNonneg(p, a, at); }
            return self.knownNonneg(p, b, at);
        }
        // Unsigned a < b with b >= 0 (signed) puts a in [0, b).
        if (fo == IROp.CmpLt || fo == IROp.CmpLe) { return self.knownNonneg(p, b, at); }
        return self.knownNonneg(p, a, at);
    }

    decideImm &self inout p:IRProgram op:IROp a:Temp c:long uns:bool at:long -> long {
        r: long = self.rel(a);
        // An exact (in)equality fact first: `a != c` says nothing an interval can.
        if (r >= 0 && (op == IROp.CmpEq || op == IROp.CmpNe)) {
            s: long = self.tfFirst.get(r);
            for k in 0..self.tfCount.get(r) {
                f: long = self.tfList.get(s + k);
                if (self.fKind.get(f) != F_REL || !self.fIsImm.get(f) || self.fA.get(f) != a || self.fImm.get(f) != c) { continue; }
                if (!self.has(at, f)) { continue; }
                if (self.fOp.get(f) == op) { return 1; }
                if (self.fOp.get(f) == negateCompare(op)) { return 0; }
            }
        }
        self.interval(p, a, at);
        if (uns) {
            // Where both are never negative the two orders agree.
            if (c < 0 || self.lo < 0) { return -1; }
        }
        return orderIntervals(op, self.lo, self.hi, c, c);
    }

    // ─── values that are never negative ──────────────────────────────────────

    // Before `computeNonneg`: per `x + y`, `x << k` and `x * y`, whether the result cannot wrap
    // past the largest value of its type when its operands are never negative (`addOk`), so that
    // `yieldsNonneg` may call it never negative when they are. The bound on an operand is what the
    // facts at that point say, or, for a temp with one definition, the bound that definition was
    // found to have (`condHi`) on the same condition: its own operands never negative. That
    // condition is exactly what `computeNonneg` then checks of every operand along the way (a
    // temp is kept never negative only while each of its definitions' operands is), so the bounds
    // hold wherever the conclusion is drawn. It is what puts `lo + width` (two values that are
    // each below a bound) and `width * 2` among the values never negative: the merge sort's
    // indexes.
    boundWalk &self inout p:IRProgram -> void {
        self.addOk.clear();
        for i in 0..self.n { self.addOk.push(false); }
        fillLong(&self.condHi, self.nt, LONG_MAX);
        self.nonneg.clear();
        for oi in 0..self.order.len() {
            b: long = self.order.get(oi);
            at: long = self.startWalk(b);
            for i in self.bStart.get(b)..self.stopOf(b) {
                in: Instr = p.code.get(self.first + i);
                o: IROp = in.op;
                hi: long = LONG_MAX;
                top: long = kindMax(in.kind);
                if (in.a != NO_TEMP && (o == IROp.Add || o == IROp.Mul)) {
                    ua: long = self.upper(p, in.a, at);
                    ub: long = LONG_MAX;
                    bc: bool = self.bConst(p, in, 0);
                    if (bc) { ub = self.cv; } else if (in.b != NO_TEMP) { ub = self.upper(p, in.b, at); }
                    if (ua >= 0 && ub >= 0) {
                        if (o == IROp.Add && ua <= top - ub) { self.addOk.set(i, true); hi = ua + ub; }
                        if (o == IROp.Mul && (ub == 0 || ua <= top / ub)) { self.addOk.set(i, true); hi = ua * ub; }
                    }
                    if (o == IROp.Add && !self.addOk.get(i) && bc && self.cv == 1 && self.belowSomething(p, in.a, in.kind, at)) {
                        self.addOk.set(i, true);
                    }
                } else if (in.a != NO_TEMP && o == IROp.Shl && in.bIsImm && in.bImm >= 1 && in.bImm <= 62) {
                    ua: long = self.upper(p, in.a, at);
                    if (ua >= 0 && ua <= (top >> in.bImm)) { self.addOk.set(i, true); hi = ua << in.bImm; }
                } else if (o == IROp.Mov && in.a != NO_TEMP) { hi = self.upper(p, in.a, at); }
                else if (o == IROp.Const) { hi = in.imm; }
                else if (in.a != NO_TEMP && self.bConst(p, in, 0)) {
                    c: long = self.cv;
                    if (o == IROp.BAnd && c >= 0) { hi = c; }
                    else if (o == IROp.Mod && c > 0) { hi = c - 1; }
                    else if (o == IROp.Div && c > 0) { ua: long = self.upper(p, in.a, at); if (ua >= 0) { hi = ua / c; } }
                    else if (o == IROp.Shr && in.bIsImm && c >= 0 && c <= 63) {
                        ua: long = self.upper(p, in.a, at);
                        if (ua >= 0) { hi = ua >> c; }
                    }
                }
                r: long = self.rel(in.dst);
                if (r >= 0 && self.defs.get(r) == 1) { self.condHi.set(r, hi); }
                self.step(p, i, at);
            }
        }
    }

    // An upper bound on `t` here: the facts' and, for one definition, what `boundWalk` found it.
    upper &self inout p:IRProgram t:Temp at:long -> long {
        self.interval(p, t, at);
        h: long = self.hi;
        r: long = self.rel(t);
        if (r >= 0 && self.defs.get(r) == 1 && self.condHi.get(r) < h) { h = self.condHi.get(r); }
        return h;
    }

    // A fact `x < y` (signed), with y no wider than the sum: x + 1 <= y, which fits.
    belowSomething &self inout p:IRProgram x:Temp k:Lit at:long -> bool {
        r: long = self.rel(x);
        if (r < 0) { return false; }
        s: long = self.tfFirst.get(r);
        for j in 0..self.tfCount.get(r) {
            f: long = self.tfList.get(s + j);
            if (self.fKind.get(f) != F_REL || self.fIsImm.get(f) || self.fUns.get(f) || !self.has(at, f)) { continue; }
            y: Temp = NO_TEMP;
            o: IROp = self.fOp.get(f);
            if (self.fA.get(f) == x && o == IROp.CmpLt) { y = self.fB.get(f); }
            if (self.fB.get(f) == x && o == IROp.CmpGt) { y = self.fA.get(f); }
            if (y == NO_TEMP) { continue; }
            if (kindWidth(k) == 8 || p.kindOf(y) == k) { return true; }
        }
        return false;
    }

    // An optimistic fixpoint: assume every temp is never negative, then strike any with a
    // definition that could produce a negative value, until nothing changes.
    computeNonneg &self inout p:IRProgram -> void {
        self.nonneg.clear();
        for r in 0..self.nt { self.nonneg.push(self.defs.get(r) > 0); }
        going: bool = true;
        while (going) {
            going = false;
            for i in 0..self.n {
                in: Instr = p.code.get(self.first + i);
                r: long = self.rel(in.dst);
                if (r < 0 || !self.nonneg.get(r)) { continue; }
                if (!self.reach.get(self.blockOf.get(i))) { continue; }
                if (!self.yieldsNonneg(p, in, i)) { self.nonneg.set(r, false); going = true; }
            }
        }
    }

    nn &self t:Temp -> bool {
        r: long = self.rel(t);
        return r >= 0 && r < self.nonneg.len() && self.nonneg.get(r);
    }

    bNonneg &self inout p:IRProgram in:Instr -> bool {
        if (in.bIsImm) { return in.bImm >= 0; }
        if (self.singleConst(p, in.b)) { return self.cv >= 0; }
        return self.nn(in.b);
    }

    yieldsNonneg &self inout p:IRProgram in:Instr i:long -> bool {
        o: IROp = in.op;
        narrowU: bool = kindUnsigned(in.kind) && kindWidth(in.kind) < 8;
        if (isFloatKind(in.kind) || (o == IROp.Convert && (isFloatKind(in.fromKind) || isFloatKind(in.toKind)))) { return false; }
        if (o == IROp.Const) { return in.imm >= 0; }
        if (o == IROp.Mov) { return self.nn(in.a); }
        if (isCompare(o)) { return true; }
        // A sized load extends what it reads; a named slot's is a whole word, as stored.
        if (o == IROp.PtrLoad) { return narrowU || in.kind == Lit.Bool; }
        if (o == IROp.Convert) {
            if (kindUnsigned(in.toKind) && kindWidth(in.toKind) < 8) { return true; }
            if (!self.nn(in.a)) { return false; }
            wt: long = kindWidth(in.toKind);
            wf: long = kindWidth(in.fromKind);
            if (wt == 8) { return true; }
            return wf < wt || (wf == wt && !kindUnsigned(in.fromKind));
        }
        if (narrowU && (o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.BAnd || o == IROp.BOr
                        || o == IROp.BXor || o == IROp.Shl || o == IROp.Shr || o == IROp.BNot
                        || o == IROp.Div || o == IROp.Mod)) { return true; }
        if (o == IROp.Add || o == IROp.Mul) { return self.addOk.get(i) && self.nn(in.a) && self.bNonneg(p, in); }
        if (o == IROp.Shl) { return in.bIsImm && self.addOk.get(i) && self.nn(in.a); }
        if (o == IROp.BAnd) { return self.nn(in.a) || self.bNonneg(p, in); }
        if (o == IROp.BOr || o == IROp.BXor) { return self.nn(in.a) && self.bNonneg(p, in); }
        if (o == IROp.Shr) {
            if (self.nn(in.a)) { return true; }
            // A logical shift by at least one clears the sign bit, at full width.
            return kindUnsigned(in.kind) && in.bIsImm && in.bImm % 64 >= 1;
        }
        if (o == IROp.Mod) { return self.nn(in.a); }
        if (o == IROp.Div) { return self.nn(in.a) && self.bNonneg(p, in); }
        return false;
    }

    // ─── copies across blocks ────────────────────────────────────────────────

    // `d = mov s` with d and s each written once: s was written before the copy on every path to
    // it, the copy before every read of d, and neither ever changes, so every read of d anywhere
    // reads s. (`opt.k` does this within a block, for any d written once.) Of the same type and
    // pointee, so nothing that asks a temp's type sees a different answer. One name for one value
    // is what lets a fact about s decide a test of d.
    shareCopies &self inout p:IRProgram -> void {
        fillLong(&self.dPos, self.nt, NO_TEMP);
        any: bool = false;
        for i in 0..self.n {
            if (p.code[self.first + i].op != IROp.Mov) { continue; }
            in: Instr = p.code.get(self.first + i);
            if (in.op != IROp.Mov) { continue; }
            d: long = self.rel(in.dst);
            s: long = self.rel(in.a);
            if (d < 0 || s < 0 || d == s || self.defs.get(d) != 1 || self.defs.get(s) != 1) { continue; }
            if (p.kindOf(in.dst) != p.kindOf(in.a) || p.pointeeOf(in.dst) != p.pointeeOf(in.a)
                || p.structOf(in.dst) != p.structOf(in.a)) { continue; }
            self.dPos.set(d, in.a);
            any = true;
        }
        if (!any) { return; }
        for i in 0..self.n {
            ix: long = self.first + i;
            in: Instr = p.code.get(ix);
            if (in.op == IROp.Nop || in.op == IROp.Label) { continue; }
            changed: bool = false;
            na: Temp = self.shared(in.a);
            if (na != in.a) { in.a = na; changed = true; }
            if (!in.bIsImm) {
                nb: Temp = self.shared(in.b);
                if (nb != in.b) { in.b = nb; changed = true; }
            }
            for k in 0..in.argCount {
                t: Temp = p.args.get(in.firstArg + k);
                nt: Temp = self.shared(t);
                if (nt != t) { p.args.set(in.firstArg + k, nt); }
            }
            for k in 0..in.pieceCount {
                t: Temp = p.asmVals.get(in.firstPiece + k);
                nt: Temp = self.shared(t);
                if (nt != t) { p.asmVals.set(in.firstPiece + k, nt); }
            }
            if (changed) { p.code.set(ix, in); self.nShared = self.nShared + 1; }
        }
    }

    // What `t` is a copy of, through any chain of such copies.
    shared &self t:Temp -> Temp {
        x: Temp = t;
        n: long = 0;
        while (n < 64) {
            r: long = self.rel(x);
            if (r < 0 || self.dPos.get(r) == NO_TEMP) { return x; }
            x = self.dPos.get(r);
            n = n + 1;
        }
        return x;
    }

    // ─── stores nothing reads ────────────────────────────────────────────────

    // A frame slot (a named one or a hidden scratch slot) whose address never escapes is reached
    // only by name or through the address constants `addressConstants` found, so every read of it
    // is in sight: a load by name, a `PtrLoad` or a block copy's source through such a constant.
    // When there is none, nothing ever observes what is written there, and every write (a store
    // by name or through a constant, a block copy or zero into it) goes. Repeated: a block copy
    // gone is one read fewer of its source. What a struct built only to be taken apart leaves,
    // once `rewrite` has forwarded its fields: the scratch it was built in, the local it was
    // copied to, and the stores into both.
    dropDeadSlots &self inout p:IRProgram -> void {
        // Only where something writes memory at all.
        writes: bool = false;
        for i in 0..self.n {
            o: IROp = p.code[self.first + i].op;
            if (o == IROp.PtrStore || o == IROp.AggCopy || o == IROp.AggZero || o == IROp.Store) { writes = true; break; }
        }
        if (!writes) { return; }
        // The address constants and the exposed slots `collectFacts` found still hold: what the
        // rewrites since made (a load become a copy, a computation a copy of an equal one) never
        // makes a new alias of a slot that was not exposed (a slot's address in memory exposed
        // it), and code removed since only reads and writes less.
        going: bool = true;
        while (going) {
            going = false;
            if (self.slotRead.cap() > 512) { self.slotRead = map![]; } else { self.slotRead.clear(); }
            any: bool = false;
            for i in 0..self.n {
                ix: long = self.first + i;
                o: IROp = p.code[ix].op;
                if (o == IROp.PtrLoad) { self.noteSlotRead(p.code[ix].a); }
                else if (o == IROp.AggCopy) { self.noteSlotRead(p.code[ix].b); any = true; }
                else if (o == IROp.Load && !p.code[ix].isGlobal && p.code[ix].name != NO_SYM) {
                    self.slotRead.put(p.code[ix].name as long, true);
                }
                else if (o == IROp.PtrStore || o == IROp.AggZero || o == IROp.Store) { any = true; }
            }
            if (!any) { return; }
            for i in 0..self.n {
                ix: long = self.first + i;
                o: IROp = p.code[ix].op;
                root: long = -1;
                if (o == IROp.PtrStore || o == IROp.AggCopy || o == IROp.AggZero) {
                    r: long = self.rel(p.code[ix].a);
                    if (r < 0 || self.acRoot.get(r) < 0 || self.acKind.get(r) != R_SLOT) { continue; }
                    root = self.acRoot.get(r);
                } else if (o == IROp.Store && !p.code[ix].isGlobal && p.code[ix].name != NO_SYM) {
                    root = p.code[ix].name as long;
                } else { continue; }
                if (self.exposed.has(root) || self.slotRead.has(root)) { continue; }
                p.code.set(ix, instr(IROp.Nop));
                self.nDeadStores = self.nDeadStores + 1;
                going = true;
            }
        }
    }

    // A read through `t`, when `t` is an address constant of a frame slot.
    noteSlotRead &self t:Temp -> void {
        r: long = self.rel(t);
        if (r < 0 || self.acRoot.get(r) < 0 || self.acKind.get(r) != R_SLOT) { return; }
        self.slotRead.put(self.acRoot.get(r), true);
    }

    // ─── the rewrite ─────────────────────────────────────────────────────────

    rewrite &self inout p:IRProgram -> void {
        fillLong(&self.dStamp, self.nt, 0);
        fillLong(&self.dPos, self.nt, -1);
        fillLong(&self.eqStamp, self.nt, 0);
        fillLong(&self.eqTo, self.nt, 0);
        fillLong(&self.eqPos, self.nt, 0);
        for oi in 0..self.order.len() {
            b: long = self.order.get(oi);
            at: long = self.startWalk(b);
            self.walkStamp = oi + 1;
            for i in self.bStart.get(b)..self.stopOf(b) {
                ix: long = self.first + i;
                in: Instr = p.code.get(ix);
                o: IROp = in.op;
                if ((o == IROp.PtrLoad || (o == IROp.Load && !in.paramSeed)) && self.instLoc.get(i) >= 0 && in.dst != NO_TEMP) {
                    v: Temp = self.knownValue(self.instLoc.get(i), in.dst, at);
                    // Through a base that is a copy of another, the location the other names.
                    if (v == NO_TEMP && o == IROp.PtrLoad) {
                        rb: Temp = self.resolve(in.a);
                        if (rb != in.a && self.rel(rb) >= 0 && self.acRoot.get(self.rel(rb)) < 0) {
                            l2: long = self.findLoc(R_TEMP, rb, in.imm, kindWidth(in.kind), loadClass(in.kind));
                            if (l2 >= 0) { v = self.knownValue(l2, in.dst, at); }
                        }
                    }
                    if (v != NO_TEMP) {
                        mv: Instr = instr(IROp.Mov);
                        mv.dst = in.dst;
                        mv.a = v;
                        mv.kind = in.kind;
                        mv.structName = in.structName;
                        p.code.set(ix, mv);
                        self.nLoads = self.nLoads + 1;
                        self.nMovs = self.nMovs + 1;
                    }
                } else if (o == IROp.Jcc && !isFloatKind(in.kind)) {
                    d: long = self.decideHere(p, in.cmpOp, in.a, in.b, in.bIsImm, in.bImm, kindUnsigned(in.kind), at, i);
                    if (d >= 0) { self.decideBranch(&in, d == 1); p.code.set(ix, in); }
                } else if (o == IROp.Jz) {
                    d: long = self.decideHere(p, IROp.CmpEq, in.a, NO_TEMP, true, 0, false, at, i);
                    if (d >= 0) { self.decideBranch(&in, d == 1); p.code.set(ix, in); }
                } else if (o == IROp.Bounds && in.a != NO_TEMP && in.b != NO_TEMP) {
                    bop: IROp = IROp.CmpLt;
                    if (in.imm == 1) { bop = IROp.CmpLe; }
                    if (self.decideHere(p, bop, in.a, in.b, false, 0, true, at, i) == 1) {
                        p.code.set(ix, instr(IROp.Nop));
                        self.nChecks = self.nChecks + 1;
                    }
                } else if (self.instExpr.get(i) >= 0 && self.reuseExpr(p, ix, i, in, at)) {
                    // computed already: now a copy
                } else if ((o == IROp.Div || o == IROp.Mod) && !kindUnsigned(in.kind) && foldableKind(in.kind)
                           && self.nn(in.a) && self.bConst(p, in, 0)) {
                    // A dividend never negative divides by 2^k as a shift, its remainder as a mask.
                    k: long = log2Exact(self.cv);
                    if (k >= 1 && (o == IROp.Div || self.cv - 1 <= IMM_HI)) {
                        if (o == IROp.Div) { in.op = IROp.Shr; in.bImm = k; }
                        else { in.op = IROp.BAnd; in.bImm = self.cv - 1; }
                        in.b = NO_TEMP;
                        in.bIsImm = true;
                        p.code.set(ix, in);
                        self.nStrength = self.nStrength + 1;
                    }
                }
                self.step(p, i, at);
                self.noteCopy(p, i);
            }
        }
    }

    // Within the block being walked, `d = mov s` makes d and s one value until either is written
    // again. A load this pass just turned into a copy reads, a few instructions on, as a different
    // temp from the one the facts name: the check after `Vec.get`'s length load compares against
    // the load's own temp.
    noteCopy &self inout p:IRProgram i:long -> void {
        in: Instr = p.code.get(self.first + i);
        r: long = self.rel(in.dst);
        if (r < 0) { return; }
        self.dStamp.set(r, self.walkStamp);
        self.dPos.set(r, i);
        if (in.op == IROp.Mov && self.rel(in.a) >= 0 && in.a != in.dst) {
            self.eqStamp.set(r, self.walkStamp);
            self.eqTo.set(r, in.a);
            self.eqPos.set(r, i);
        } else {
            self.eqStamp.set(r, 0);
        }
    }

    // The temp `t` is a copy of here, or `t`.
    resolve &self t:Temp -> Temp {
        r: long = self.rel(t);
        if (r < 0 || self.eqStamp.get(r) != self.walkStamp) { return t; }
        v: Temp = self.eqTo.get(r);
        vr: long = self.rel(v);
        if (self.dStamp.get(vr) == self.walkStamp && self.dPos.get(vr) > self.eqPos.get(r)) { return t; }
        return v;
    }

    decideHere &self inout p:IRProgram op:IROp a:Temp b:Temp isImm:bool imm:long uns:bool at:long i:long -> long {
        d: long = self.decide(p, op, a, b, isImm, imm, uns, at);
        if (d >= 0) { return d; }
        ra: Temp = self.resolve(a);
        rb: Temp = b;
        if (!isImm) { rb = self.resolve(b); }
        if (ra != a || rb != b) {
            d = self.decide(p, op, ra, rb, isImm, imm, uns, at);
            if (d >= 0) { return d; }
        }
        // Through copies this pass made in other blocks (a load it found the value of): `d = mov
        // s`, both written once, is s wherever d is read (`shareCopies`' argument).
        ca: Temp = self.copySource(p, ra);
        cb: Temp = rb;
        if (!isImm) { cb = self.copySource(p, rb); }
        if (ca == ra && cb == rb) { return -1; }
        return self.decide(p, op, ca, cb, isImm, imm, uns, at);
    }

    // What `t` is a copy of, through copies whose two sides are each written once.
    copySource &self inout p:IRProgram t:Temp -> Temp {
        x: Temp = t;
        n: long = 0;
        while (n < 8) {
            r: long = self.rel(x);
            if (r < 0 || self.defs.get(r) != 1 || self.defAt.get(r) < 0) { return x; }
            ix: long = self.first + self.defAt.get(r);
            if (p.code[ix].op != IROp.Mov) { return x; }
            s: Temp = p.code[ix].a;
            sr: long = self.rel(s);
            if (sr < 0 || s == x || self.defs.get(sr) != 1) { return x; }
            x = s;
            n = n + 1;
        }
        return x;
    }

    // `x op y` at the type's width and signedness, as the emitted instruction computes it; false
    // where it must stay for the machine to do (a division by zero, the one that overflows, a shift
    // count the emitter would spell differently). The result is left in `cv`.
    evalArith &self o:IROp x:long y:long k:Lit yImm:bool -> bool {
        uns: bool = kindUnsigned(k);
        v: long = 0;
        if (o == IROp.Add) { v = x + y; }
        else if (o == IROp.Sub) { v = x - y; }
        else if (o == IROp.Mul) { v = x * y; }
        else if (o == IROp.BAnd) { v = x & y; }
        else if (o == IROp.BOr) { v = x | y; }
        else if (o == IROp.BXor) { v = x ^ y; }
        else if (o == IROp.Div || o == IROp.Mod) {
            if (y == 0) { return false; }
            if (uns) {
                ux: u64 = x as u64;
                uy: u64 = y as u64;
                if (o == IROp.Div) { v = (ux / uy) as long; } else { v = (ux % uy) as long; }
            } else {
                if (y == -1 && x == LONG_MIN) { return false; }
                if (o == IROp.Div) { v = x / y; } else { v = x % y; }
            }
        }
        else if (o == IROp.Shl || o == IROp.Shr) {
            // An immediate count is emitted as `count % 64`, a register one masked by the hardware.
            if (yImm && y < 0) { return false; }
            c: long = y & 63;
            if (o == IROp.Shl) { v = x << c; }
            else if (uns) { v = ((x as u64) >> (c as u64)) as long; }
            else { v = x >> c; }
        }
        else { return false; }
        self.cv = canon(k, v);
        return true;
    }

    // The temp known to hold location `l` here, other than `dst` itself, or NO_TEMP.
    knownValue &self l:long dst:Temp at:long -> Temp {
        f: long = self.locFactHead.get(l);
        while (f >= 0) {
            if (self.has(at, f) && self.fA.get(f) != dst) { return self.fA.get(f); }
            f = self.factNext.get(f);
        }
        return NO_TEMP;
    }
}

// ─── helpers ─────────────────────────────────────────────────────────────────

// `v` as `n` copies of `x`. What it already holds is overwritten in place, and only the rest
// pushed: this runs a dozen times per function, and a push is a call where a write is not.
local fillBool inout v:Vec<bool> n:long x:bool -> void {
    if (v.len() > n) { v.truncate(n); }
    for i in 0..v.len() { v.set(i, x); }
    while (v.len() < n) { v.push(x); }
}

local fillLong inout v:Vec<long> n:long x:long -> void {
    if (v.len() > n) { v.truncate(n); }
    for i in 0..v.len() { v.set(i, x); }
    while (v.len() < n) { v.push(x); }
}

local setBit inout v:Vec<long> at:long f:long -> void {
    w: long = at + f / 64;
    v.set(w, v.get(w) | (1 << (f % 64)));
}

// A hash step for the fact and location tables' keys. A collision costs a missed merge, never a
// wrong one: every hit is compared field by field.
local mix h:long x:long -> long {
    return (h ^ x) * 1099511628211 + 1469598103934665603;
}

local isArith o:IROp -> bool {
    return o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.Div || o == IROp.Mod
        || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor || o == IROp.Shl || o == IROp.Shr;
}

local isFloatKind k:Lit -> bool { return k == Lit.Float || k == Lit.Double; }

// The types whose values this pass computes with: integers, `bool`, pointers.
local foldableKind k:Lit -> bool {
    return k == Lit.Int || k == Lit.Long || k == Lit.Char || k == Lit.I16 || k == Lit.U8 || k == Lit.U16
        || k == Lit.U32 || k == Lit.U64 || k == Lit.Bool || k == Lit.Ptr || k == Lit.Ref;
}

local convertible k:Lit -> bool { return foldableKind(k) || k == Lit.Struct; }

// How many bytes a value of this type is read and written as (the emitter's `widthOf`), and
// whether it extends with zeroes. `typeInfo` is a hash lookup and these are asked per access, so
// each answer is kept, by tag, the first time it is asked.
local var gKindCode: Vec<long>;

local kindCode k:Lit -> long {
    i: long = k as long;
    if (i < gKindCode.len() && gKindCode.get(i) > 0) { return gKindCode.get(i); }
    ti: TypeInfo = typeInfo(k);
    w: long = ti.size;
    if (w < 1 || w > 8) { w = 8; }
    else if (w == 3) { w = 4; }
    else if (w > 4) { w = 8; }
    c: long = w * 2;
    if (ti.unsignedNum) { c = c + 1; }
    while (gKindCode.len() <= i) { gKindCode.push(0); }
    gKindCode.set(i, c);
    return c;
}

local kindWidth k:Lit -> long { return kindCode(k) / 2; }
local kindUnsigned k:Lit -> bool { return kindCode(k) % 2 == 1; }

// What a load of this type leaves in a register depends on its width and on how it extends.
local loadClass k:Lit -> long {
    w: long = kindWidth(k);
    if (w < 8 && kindUnsigned(k)) { return w * 2 + 1; }
    return w * 2;
}

// A store's value reads back unchanged when the store writes the whole register, or when the
// value already has the type it is stored as.
local forwardable store:Lit value:Lit -> bool {
    if (isAggregate(store)) { return false; }
    if (kindWidth(store) == 8) { return true; }
    return loadClass(store) == loadClass(value) && !isAggregate(value);
}

// The largest value of a type's canonical form.
local kindMax k:Lit -> long {
    w: long = kindWidth(k);
    if (w >= 8) { return LONG_MAX; }
    if (kindUnsigned(k)) { return (1 << (w * 8)) - 1; }
    return (1 << (w * 8 - 1)) - 1;
}

// A value as a register of type `k` holds it: the low bytes, extended by the type's signedness.
local canon k:Lit v:long -> long {
    w: long = kindWidth(k);
    if (w >= 8) { return v; }
    bitsN: long = w * 8;
    if (kindUnsigned(k)) { return v & ((1 << bitsN) - 1); }
    sh: long = 64 - bitsN;
    return (v << sh) >> sh;
}

local boolWord b:bool -> long { if (b) { return 1; } return 0; }

local makeConst inout in:Instr v:long -> void {
    d: Temp = in.dst;
    k: Lit = in.kind;
    s: Sym = in.structName;
    if (in.op == IROp.Convert) { k = in.toKind; }
    in = instr(IROp.Const);
    in.dst = d;
    in.imm = v;
    in.kind = k;
    in.structName = s;
}

local makeMov inout in:Instr src:Temp -> void {
    d: Temp = in.dst;
    k: Lit = in.kind;
    s: Sym = in.structName;
    in = instr(IROp.Mov);
    in.dst = d;
    in.a = src;
    in.kind = k;
    in.structName = s;
}

// k when v == 2^k (k in 1..62), else -1.
local log2Exact v:long -> long {
    if (v <= 1 || (v & (v - 1)) != 0) { return -1; }
    k: long = 0;
    while ((1 << k) != v) { k = k + 1; }
    if (k > 62) { return -1; }
    return k;
}

local compareHolds op:IROp x:long y:long uns:bool -> bool {
    if (op == IROp.CmpEq) { return x == y; }
    if (op == IROp.CmpNe) { return x != y; }
    if (uns) {
        ux: u64 = x as u64;
        uy: u64 = y as u64;
        if (op == IROp.CmpLt) { return ux < uy; }
        if (op == IROp.CmpLe) { return ux <= uy; }
        if (op == IROp.CmpGt) { return ux > uy; }
        return ux >= uy;
    }
    if (op == IROp.CmpLt) { return x < y; }
    if (op == IROp.CmpLe) { return x <= y; }
    if (op == IROp.CmpGt) { return x > y; }
    return x >= y;
}

// The comparison as `support::fp` numbers it.
local fpOp op:IROp -> long {
    if (op == IROp.CmpEq) { return 0; }
    if (op == IROp.CmpNe) { return 1; }
    if (op == IROp.CmpLt) { return 2; }
    if (op == IROp.CmpLe) { return 3; }
    if (op == IROp.CmpGt) { return 4; }
    return 5;
}

// `b op a` for `a op b`.
local swapCompare op:IROp -> IROp {
    if (op == IROp.CmpLt) { return IROp.CmpGt; }
    if (op == IROp.CmpGt) { return IROp.CmpLt; }
    if (op == IROp.CmpLe) { return IROp.CmpGe; }
    if (op == IROp.CmpGe) { return IROp.CmpLe; }
    return op;
}

// Whether `x f y` guarantees `x q y`.
local implies f:IROp q:IROp -> bool {
    if (f == q) { return true; }
    if (f == IROp.CmpLt) { return q == IROp.CmpLe || q == IROp.CmpNe; }
    if (f == IROp.CmpGt) { return q == IROp.CmpGe || q == IROp.CmpNe; }
    if (f == IROp.CmpEq) { return q == IROp.CmpLe || q == IROp.CmpGe; }
    return false;
}

// `a op b` decided by intervals: a in [alo, ahi], b in [blo, bhi], signed.
local orderIntervals op:IROp alo:long ahi:long blo:long bhi:long -> long {
    if (alo > ahi || blo > bhi) { return -1; }
    if (op == IROp.CmpLt) { if (ahi < blo) { return 1; } if (alo >= bhi) { return 0; } return -1; }
    if (op == IROp.CmpLe) { if (ahi <= blo) { return 1; } if (alo > bhi) { return 0; } return -1; }
    if (op == IROp.CmpGt) { if (alo > bhi) { return 1; } if (ahi <= blo) { return 0; } return -1; }
    if (op == IROp.CmpGe) { if (alo >= bhi) { return 1; } if (ahi < blo) { return 0; } return -1; }
    if (op == IROp.CmpEq) {
        if (alo == ahi && blo == bhi && alo == blo) { return 1; }
        if (ahi < blo || bhi < alo) { return 0; }
        return -1;
    }
    if (alo == ahi && blo == bhi && alo == blo) { return 0; }
    if (ahi < blo || bhi < alo) { return 1; }
    return -1;
}
