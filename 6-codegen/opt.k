// The local optimizer: six small passes over one function at a time, over the flat instruction
// run its `IRFunc` names. `flow.k` does the work that needs to see across blocks.
//
// Every rewrite is made in place, and an unwanted instruction becomes a `Nop` rather than being
// removed, since each `IRFunc` after it names its own run by index. `runOne` runs the passes in
// the order they depend on: promotion first, because it turns slots into the copies the next two
// passes remove; `fuseBranches` reuses the use counts `selectImmediates` took; and dead
// definitions go last, once the other passes have left them unread. What decides whether a change
// here is right is the corpus's output, not its assembly.
#include <{cfg, ir}>
#include <parse::types>
#include <support::compiler>
#include <stdlib::{map, option, string, vec}>

// How many times a pass will go round before giving up. Each one shrinks the function, so this
// is a guard against a rewrite that undoes itself rather than a real bound.
local MAX_ROUNDS: long = 8;

// A 32-bit signed immediate is what an x86-64 arithmetic or compare instruction encodes. A wider
// constant stays in a register.
local IMM_MIN: long = 0 - 2147483648;
local IMM_MAX: long = 2147483647;

pub struct Opt {
    // Per temp of the function being worked on, indexed by `t - base`.
    uses: Vec<long>,        // how many instructions read it
    defs: Vec<long>,        // how many write it
    defAt: Vec<long>,       // the single defining instruction, when there is exactly one
    base: Temp,

    // Locals promoted to temps: the variable's name -> the temp that now holds it.
    slotTemp: HashMap<long, Temp>,
    // Names this function may not promote: their address is taken, they are globals, or an `asm`
    // block spells them.
    pinned: HashMap<long, bool>,
    // Labels some branch names (`dropUnusedLabels`).
    named: HashMap<long, bool>,
    // `copyRound`, per temp of the function: the copy it is (block stamp, source, the source's
    // write count then) and its own write count in the block being walked.
    cpStamp: Vec<long>, cpTo: Vec<long>, cpVer: Vec<long>, vStamp: Vec<long>, vCount: Vec<long>, blkSeq: long,
    afterInline: bool,      // the run over spliced code (main.k sets it)
    ddStack: Vec<long>,     // `dropIfDead`: the instructions whose results may have no reader left
    ddAgain: bool,          // and a temp of several definitions left unread, for another walk
    urMap: Vec<long>,       // `unrollAll`: each of the function's temps, renumbered
    urBase: long,           // and where the renumbered run starts

    // Counters, for `--trace-opt`.
    nPromoted: long, nCopies: long, nImm: long, nFused: long, nJumps: long, nDead: long
}

pub var gTraceOpt: bool = false;
// `--no-empty-loops`: a branch to the next instruction and a loop that does nothing anyone sees
// are left as they are (`dropEmptyLoops`).
pub var gEmptyLoopsOff: bool = false;
// `--no-fill-loops`: a loop that only clears a range stays a loop (`fillLoop`).
pub var gFillLoopsOff: bool = false;
// An `asm` block's one output, into a local that nothing else pins, written straight into the
// local's temp (`asmOutName`), not stored to its slot (`--no-asm-out`).
pub var gAsmOutOff: bool = false;
// A counted loop of a few straight-line instructions run two turns at a time (`unrollLoop`,
// `--no-unroll`).
pub var gUnrollOff: bool = false;
// A branch decided again once dead definitions are gone, a fused compare and branch of two
// constants among them (`foldConstBranches`, `--no-refold`).
pub var gRefoldOff: bool = false;
// The most instructions, the counter's step among them, a body two turns are made of may have.
local UNROLL_MAX: long = 12;
var gUnrollSeq: long = 0;

methods Opt for Default {
    new -> Opt {
        return Opt { uses: vec![], defs: vec![], defAt: vec![], base: 0,
                     slotTemp: map![], pinned: map![], named: map![],
                     cpStamp: vec![], cpTo: vec![], cpVer: vec![], vStamp: vec![], vCount: vec![], blkSeq: 0, afterInline: false, ddStack: vec![], ddAgain: false, urMap: vec![], urBase: 0,
                     nPromoted: 0, nCopies: 0, nImm: 0, nFused: 0, nJumps: 0, nDead: 0 };
    }
}

methods Opt {
    run &self inout p:IRProgram -> void {
        for f in 0..p.funcs.len() {
            self.runOne(p, p.funcs.get(f));
        }
        if (gTraceOpt) {
            eprintln("opt: {} locals promoted, {} copies removed, {} immediates, {} branches fused, {} jumps removed, {} dead",
                     self.nPromoted, self.nCopies, self.nImm, self.nFused, self.nJumps, self.nDead);
        }
    }

    runOne &self inout p:IRProgram fn:IRFunc -> void {
        if (fn.instrCount == 0) { return; }
        self.base = fn.firstTemp;
        self.promoteLocals(p, fn);
        if (self.foldConstBranches(p, fn)) { self.dropUnreachable(p, fn); }
        // Jumps to the next instruction first (an inlined body's `ret`s), so the labels they named
        // stop splitting blocks before the block-local passes run.
        if (self.afterInline) {
            self.simplifyJumps(p, fn);
            self.dropUnusedLabels(p, fn);
        }
        self.propagateCopies(p, fn);
        self.coalesceMoves(p, fn);
        self.selectImmediates(p, fn);
        self.fuseBranches(p, fn);
        self.simplifyJumps(p, fn);
        self.dropUnusedLabels(p, fn);
        dead: long = self.nDead;
        self.dropDeadDefs(p, fn);
        // Once more where that removed something: a copy of an inlined body's result, or the
        // branch on a comparison it returned, can be the value's only reader just now, when a
        // dead second copy has gone. With the counts `dropDeadDefs` took last (see
        // `coalesceRound`), so this costs no walk of its own.
        if (self.nDead > dead) {
            // What died may leave a branch to the next instruction, and a loop with nothing left
            // in it (a drop loop over values that need no drop).
            if (!gEmptyLoopsOff) {
                j0: long = self.nJumps;
                self.simplifyJumps(p, fn);
                self.countUses(p, fn);
                if (self.dropEmptyLoops(p, fn) || self.nJumps > j0) {
                    self.simplifyJumps(p, fn);
                    self.dropUnusedLabels(p, fn);
                    self.dropDeadDefs(p, fn);
                }
            }
            self.coalesceRound(p, fn);
            self.fuseBranches(p, fn);
        }
        // A branch the passes above made a test of constants is decided now: a drop flag is the
        // common one, set where the value moves and tested by the drop at the exit, whose test
        // copies and dead definitions left as a compare of two constants. Before inlining is
        // when that matters: the drop hands the address of a by-value parameter to a call, and
        // that keeps the body from being copied anywhere.
        if (!gRefoldOff && self.foldConstBranches(p, fn)) {
            self.dropUnreachable(p, fn);
            self.simplifyJumps(p, fn);
            self.dropUnusedLabels(p, fn);
            self.dropDeadDefs(p, fn);
        }
    }

    // ─── loops that only clear a range ──────────────────────────────────────

    // Over every function, once element addresses are one addressing mode each (`scale.k`).
    fillLoopsAll &self inout p:IRProgram -> void {
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            if (fn.instrCount == 0) { continue; }
            self.base = fn.firstTemp;
            self.countUses(p, fn);
            for j in 0..fn.instrCount {
                jx: long = fn.firstInstr + j;
                if (p.code[jx].op != IROp.Jmp) { continue; }
                hn: Sym = p.code[jx].name;
                h: long = j - 1;
                while (h >= 0 && !(p.code[fn.firstInstr + h].op == IROp.Label && p.code[fn.firstInstr + h].name == hn)) { h = h - 1; }
                if (h >= 0) { self.fillLoop(p, fn, h, j); }
            }
        }
    }

    // Every function's counted loops that `unrollLoop` takes, two turns at a time. Run last, on
    // the IR the emitter reads. A function with one is written out again at the end of the
    // program's instructions, and its temps renumbered into a new run at the end of the program's
    // (`urTemp`), with room for the temps each extra copy of a body gets: a temp the body writes
    // before it reads and nothing outside reads (`urLocal`) is a new one in each copy, so that each
    // copy's live ranges end where that copy ends, as the allocator's single span per temp needs.
    unrollAll &self inout p:IRProgram -> void {
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            if (fn.instrCount == 0) { continue; }
            self.base = fn.firstTemp;
            self.countUses(p, fn);
            heads: Vec<long>;
            ends: Vec<long>;
            for j in 0..fn.instrCount {
                jx: long = fn.firstInstr + j;
                if (p.code[jx].op != IROp.Jmp) { continue; }
                hn: Sym = p.code[jx].name;
                h: long = j - 1;
                while (h >= 0 && !(p.code[fn.firstInstr + h].op == IROp.Label && p.code[fn.firstInstr + h].name == hn)) { h = h - 1; }
                if (h >= 0 && self.unrollable(p, fn, h, j)) { heads.push(h); ends.push(j); }
            }
            if (heads.len() == 0) { continue; }
            // The function's temps, renumbered: each old one's copy first, in order.
            n: long = fn.tempCount - fn.firstTemp;
            nb: Temp = p.tempKinds.len();
            for t in fn.firstTemp..fn.tempCount { self.copyTemp(p, t); }
            self.urMap.clear();
            for r in 0..n { self.urMap.push(nb + r); }
            self.urBase = nb;
            start: long = p.code.len();
            next: long = 0;
            i: long = 0;
            while (i < fn.instrCount) {
                if (next < heads.len() && heads.get(next) == i) {
                    self.unrollLoop(p, fn, heads.get(next), ends.get(next));
                    i = ends.get(next) + 1;
                    next = next + 1;
                    continue;
                }
                in: Instr = p.code.get(fn.firstInstr + i);
                self.urRename(p, &in, true);
                p.code.push(in);
                i = i + 1;
            }
            fn.firstInstr = start;
            fn.instrCount = p.code.len() - start;
            fn.firstTemp = nb;
            fn.tempCount = p.tempKinds.len();
            p.funcs.set(f, fn);
        }
    }

    // A new temp like `t`: its type, companion name and pointee.
    copyTemp &self inout p:IRProgram t:Temp -> Temp {
        c: Temp = p.newTemp(p.tempKinds.get(t), p.tempStructs.get(t));
        p.tempPointees.set(c, p.tempPointees.get(t));
        return c;
    }

    // `in`'s temps as the renumbered function names them (`urMap`); with `runs`, its call
    // arguments and `asm` values too, which are rewritten where they lie (each instruction outside
    // an unrolled body is written once, and a body has none).
    urRename &self inout p:IRProgram inout in:Instr runs:bool -> void {
        in.dst = self.urTemp(in.dst);
        in.a = self.urTemp(in.a);
        if (!in.bIsImm) { in.b = self.urTemp(in.b); }
        in.x = self.urTemp(in.x);
        if (!runs) { return; }
        for k in 0..in.argCount { p.args.set(in.firstArg + k, self.urTemp(p.args.get(in.firstArg + k))); }
        for k in 0..in.pieceCount { p.asmVals.set(in.firstPiece + k, self.urTemp(p.asmVals.get(in.firstPiece + k))); }
    }

    urTemp &self t:Temp -> Temp {
        r: long = t - self.base;
        if (t == NO_TEMP || r < 0 || r >= self.urMap.len()) { return t; }
        return self.urMap.get(r);
    }

    // The temps body `t + 1..j` writes before it reads them and nothing outside it reads or
    // writes: a new temp each in every copy past the first.
    urLocal &self inout p:IRProgram fn:IRFunc t:long j:long -> Vec<long> {
        out: Vec<long>;
        for k in t + 1..j {
            d: Temp = p.code[fn.firstInstr + k].dst;
            r: long = d - self.base;
            if (d == NO_TEMP || r < 0 || r >= self.defs.len()) { continue; }
            seen: bool = false;
            for q in 0..out.len() { if (out.get(q) == r) { seen = true; } }
            if (seen) { continue; }
            within: long = 0;
            for q in t + 1..j { if (p.code[fn.firstInstr + q].dst == d) { within = within + 1; } }
            if (within != self.defs.get(r)) { continue; }
            if (self.usesWithin(p, fn, d, t + 1, j - 1) != self.usesWithin(p, fn, d, 0, fn.instrCount - 1)) { continue; }
            // Read in the body before it is written there: the value comes round from the turn before.
            early: bool = false;
            for q in t + 1..k + 1 {
                if (self.usesWithin(p, fn, d, q, q) > 0) { early = true; }
                if (q < k && p.code[fn.firstInstr + q].dst == d) { break; }
            }
            if (early) { continue; }
            out.push(r);
        }
        return out;
    }

    // Loop `h..j`, top-tested, `H: if (i >= n) goto X; body; goto H` with `X:` just after it, taken
    // two turns at a time: the body a few straight-line instructions with nothing to branch to
    // (no label, branch, call, `asm` block or block copy), `i = i + 1` once in it at the test's
    // width, `n` a constant or a temp written once, before the loop, read by the test alone, and
    // `H` reached only from above and from the jump back.
    unrollable &self inout p:IRProgram fn:IRFunc h:long j:long -> bool {
        if (gUnrollOff) { return false; }
        t: long = h + 1;
        while (t < j && p.code[fn.firstInstr + t].op == IROp.Nop) { t = t + 1; }
        if (t >= j) { return false; }
        test: Instr = p.code.get(fn.firstInstr + t);
        if (test.op != IROp.Jcc || test.cmpOp != IROp.CmpGe || isFloat(test.kind) || test.a == NO_TEMP) { return false; }
        ctr: Temp = test.a;
        if (test.bIsImm) {
            if (test.bImm <= 0 - 2147483648) { return false; }
        } else {
            nt: Temp = test.b;
            if (nt == NO_TEMP || nt == ctr || nt - self.base < 0 || nt - self.base >= self.defs.len()) { return false; }
            if (self.usesWithin(p, fn, nt, 0, fn.instrCount - 1) != 1) { return false; }
        }
        x: long = j + 1;
        while (x < fn.instrCount && p.code[fn.firstInstr + x].op == IROp.Nop) { x = x + 1; }
        if (x >= fn.instrCount || p.code[fn.firstInstr + x].op != IROp.Label || p.code[fn.firstInstr + x].name != test.name) { return false; }
        if (self.namedOutside(p, fn, p.code[fn.firstInstr + h].name, h, j)) { return false; }
        size: long = 0;
        steps: long = 0;
        for k in t + 1..j {
            in: Instr = p.code.get(fn.firstInstr + k);
            o: IROp = in.op;
            if (o == IROp.Nop) { continue; }
            if (!(o == IROp.Const || o == IROp.Mov || o == IROp.Add || o == IROp.Sub || o == IROp.Mul
                  || o == IROp.Div || o == IROp.Mod || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor
                  || o == IROp.Shl || o == IROp.Shr || o == IROp.BNot || o == IROp.Convert || isCompare(o)
                  || o == IROp.PtrLoad || o == IROp.PtrStore || o == IROp.Load || o == IROp.Store)) { return false; }
            size = size + 1;
            if (in.dst != NO_TEMP && in.dst == test.b && !test.bIsImm) { return false; }
            if (in.dst == ctr) {
                if (o != IROp.Add || in.a != ctr || !in.bIsImm || in.bImm != 1 || in.kind != test.kind) { return false; }
                steps = steps + 1;
            }
        }
        return steps == 1 && size <= UNROLL_MAX;
    }

    // Writes loop `h..j` (which `unrollable` took) at the end of the program's instructions:
    //
    //     if (i >= n) goto X; n = n - 1;           the test once, then the bound less one
    //     H: if (i >= n) goto T; body; body; goto H
    //     T: n = n + 1; if (i >= n) goto X; body   the bound back, and the turn an odd count leaves
    //
    // Before `H` at least one turn remains, so `n` is past the smallest value and `n - 1` does
    // not wrap; at `H`, `i < n - 1` leaves two turns; at `T`, `i` is `n - 1` (one turn) or `n`.
    // `n` is put back on the way out, as the loop may be entered again (an outer loop's next turn)
    // with nothing writing it in between. A constant bound is lowered by one in the pair's test.
    unrollLoop &self inout p:IRProgram fn:IRFunc h:long j:long -> void {
        t: long = h + 1;
        while (p.code[fn.firstInstr + t].op == IROp.Nop) { t = t + 1; }
        locals: Vec<long> = self.urLocal(p, fn, t, j);
        test: Instr = p.code.get(fn.firstInstr + t);
        self.urRename(p, &test, false);
        p.code.push(test);
        if (!test.bIsImm) {
            dec: Instr = instr(IROp.Sub);
            dec.dst = test.b;
            dec.a = test.b;
            dec.bIsImm = true;
            dec.bImm = 1;
            dec.kind = p.kindOf(test.b);
            p.code.push(dec);
        }
        tail: Sym = internString(format(".UT{}", gUnrollSeq));
        gUnrollSeq = gUnrollSeq + 1;
        p.code.push(p.code.get(fn.firstInstr + h));
        pair: Instr = test;
        pair.name = tail;
        if (test.bIsImm) { pair.bImm = test.bImm - 1; }
        p.code.push(pair);
        self.urBody(p, fn, t, j, &locals, false);
        self.urBody(p, fn, t, j, &locals, true);
        p.code.push(p.code.get(fn.firstInstr + j));
        lb: Instr = instr(IROp.Label);
        lb.name = tail;
        p.code.push(lb);
        if (!test.bIsImm) {
            inc: Instr = instr(IROp.Add);
            inc.dst = test.b;
            inc.a = test.b;
            inc.bIsImm = true;
            inc.bImm = 1;
            inc.kind = p.kindOf(test.b);
            p.code.push(inc);
        }
        p.code.push(test);
        self.urBody(p, fn, t, j, &locals, true);
        // The body's own temps under their renumbered names again, for whatever follows.
        for q in 0..locals.len() { self.urMap.set(locals.get(q), self.urBase + locals.get(q)); }
    }

    // One copy of body `t + 1..j` at the end of the program's instructions, renamed; with `fresh`,
    // each of the body's own temps (`locals`) a new one for this copy.
    urBody &self inout p:IRProgram fn:IRFunc t:long j:long inout locals:Vec<long> fresh:bool -> void {
        if (fresh) {
            for q in 0..locals.len() {
                r: long = locals.get(q);
                self.urMap.set(r, self.copyTemp(p, self.base + r));
            }
        }
        for k in t + 1..j {
            if (p.code[fn.firstInstr + k].op == IROp.Nop) { continue; }
            in: Instr = p.code.get(fn.firstInstr + k);
            self.urRename(p, &in, false);
            p.code.push(in);
        }
    }

    // `i = A; H: if (i >= N) goto X; [i*w + o] of a frame slot's array = 0; i = i + 1; goto H`,
    // A and N constants and `w` the store's width: one block zero (`AggZero`) of the bytes it
    // clears, which the emitter writes as stores up to a few words and as `rep stosq` past them.
    // Nothing else may happen in the loop, and the counter is read nowhere after it.
    fillLoop &self inout p:IRProgram fn:IRFunc h:long j:long -> void {
        t: long = h + 1;
        while (t < j && (p.code[fn.firstInstr + t].op == IROp.Nop || p.code[fn.firstInstr + t].op == IROp.Label)) { t = t + 1; }
        if (t >= j) { return; }
        test: Instr = p.code.get(fn.firstInstr + t);
        if (test.op != IROp.Jcc || test.cmpOp != IROp.CmpGe || isFloat(test.kind) || !test.bIsImm) { return; }
        ctr: Temp = test.a;
        if (ctr == NO_TEMP) { return; }
        // The counter's start, written just before the loop.
        k: long = h - 1;
        while (k >= 0 && p.code[fn.firstInstr + k].op == IROp.Nop) { k = k - 1; }
        if (k < 0) { return; }
        init: Instr = p.code.get(fn.firstInstr + k);
        if (init.op != IROp.Const || init.dst != ctr) { return; }
        st: long = -1;
        steps: long = 0;
        for m in h + 1..j {
            ix: long = fn.firstInstr + m;
            o: IROp = p.code[ix].op;
            if (o == IROp.Nop || m == t) { continue; }
            if (o == IROp.Label) {
                if (self.namedOutside(p, fn, p.code[ix].name, h, j)) { return; }
                continue;
            }
            in: Instr = p.code.get(ix);
            if (o == IROp.PtrStore) {
                if (st >= 0) { return; }
                st = m;
                continue;
            }
            if (o == IROp.Add && in.dst == ctr) {
                if (in.a != ctr || in.kind != test.kind || !(in.bIsImm && in.bImm == 1)) { return; }
                steps = steps + 1;
                continue;
            }
            if ((o != IROp.Const && o != IROp.AddrOf) || in.dst == NO_TEMP || in.dst == ctr) { return; }
            if (self.usesWithin(p, fn, in.dst, h, j) != self.usesWithin(p, fn, in.dst, 0, fn.instrCount - 1)) { return; }
        }
        if (st < 0 || steps != 1) { return; }
        // Read nowhere but in the loop (its start aside, which is no read).
        if (self.usesWithin(p, fn, ctr, h, j) != self.usesWithin(p, fn, ctr, 0, fn.instrCount - 1)) { return; }
        s: Instr = p.code.get(fn.firstInstr + st);
        w: long = widthOf(s.kind);
        if (s.x != ctr || s.scale != w || isFloat(s.kind) || isAggregate(s.kind) || s.a == NO_TEMP) { return; }
        if (!(s.bIsImm && s.bImm == 0) && !self.isZero(p, fn, s.b)) { return; }
        // The base: a frame slot's address, written once.
        bi: long = s.a - self.base;
        if (bi < 0 || bi >= self.defs.len() || self.defs.get(bi) != 1) { return; }
        bd: long = self.defAt.get(bi);
        bdef: Instr = p.code.get(fn.firstInstr + bd);
        if (bdef.op != IROp.AddrOf || bdef.isGlobal || bdef.name == NO_SYM) { return; }
        a0: long = init.imm;
        n0: long = test.bImm;
        if (a0 * w + s.imm != 0 || a0 < 0) { return; }
        bytes: long = 0;
        if (n0 > a0) { bytes = (n0 - a0) * w; }
        // Past the slot's own bytes it is not this rewrite's to judge.
        if (bytes > p.fnSlotBytesOf(fn.name, bdef.name)) { return; }
        exitL: Sym = test.name;
        follows: bool = self.nextLabelIs(p, fn, j + 1, exitL);
        for m in h + 1..j + 1 { p.code.set(fn.firstInstr + m, instr(IROp.Nop)); }
        at: long = h + 1;
        if (bytes > 0) {
            if (bd > h && bd < j) { p.code.set(fn.firstInstr + at, bdef); at = at + 1; }
            z: Instr = instr(IROp.AggZero);
            z.a = s.a;
            z.imm = bytes;
            p.code.set(fn.firstInstr + at, z);
            at = at + 1;
        }
        if (!follows) {
            jx: Instr = instr(IROp.Jmp);
            jx.name = exitL;
            p.code.set(fn.firstInstr + at, jx);
        }
        self.nJumps = self.nJumps + 1;
    }

    // `t` is written once, by the constant 0.
    isZero &self inout p:IRProgram fn:IRFunc t:Temp -> bool {
        i: long = t - self.base;
        if (t == NO_TEMP || i < 0 || i >= self.defs.len() || self.defs.get(i) != 1) { return false; }
        d: long = self.defAt.get(i);
        return d >= 0 && p.code[fn.firstInstr + d].op == IROp.Const && p.code[fn.firstInstr + d].imm == 0;
    }

    // A counted loop that does nothing anyone sees: `H: if (i >= n) goto X; ...; i = i + 1; goto
    // H`, with nothing between but arithmetic on temps no instruction outside the loop reads, no
    // branch but those two, and `n` written nowhere in it. It ends (the counter steps by one
    // toward a bound of its own width, and every trip passes the test), so it is a jump to X.
    // What is left of a drop loop over elements whose drop does nothing (`Vec.truncate`,
    // `HashMap.clear` once their loads are gone). Answers whether it removed one.
    dropEmptyLoops &self inout p:IRProgram fn:IRFunc -> bool {
        any: bool = false;
        for j in 0..fn.instrCount {
            jx: long = fn.firstInstr + j;
            if (p.code[jx].op != IROp.Jmp) { continue; }
            hn: Sym = p.code[jx].name;
            h: long = j - 1;
            while (h >= 0 && !(p.code[fn.firstInstr + h].op == IROp.Label && p.code[fn.firstInstr + h].name == hn)) { h = h - 1; }
            if (h < 0) { continue; }
            if (self.emptyLoop(p, fn, h, j)) { any = true; }
        }
        return any;
    }

    emptyLoop &self inout p:IRProgram fn:IRFunc h:long j:long -> bool {
        // The test, the first thing the header does.
        t: long = h + 1;
        while (t < j && (p.code[fn.firstInstr + t].op == IROp.Nop || p.code[fn.firstInstr + t].op == IROp.Label)) { t = t + 1; }
        if (t >= j) { return false; }
        test: Instr = p.code.get(fn.firstInstr + t);
        if (test.op != IROp.Jcc || (test.cmpOp != IROp.CmpGe && test.cmpOp != IROp.CmpEq) || isFloat(test.kind)) { return false; }
        ctr: Temp = test.a;
        if (ctr == NO_TEMP || (!test.bIsImm && (test.b == NO_TEMP || test.b == ctr))) { return false; }
        steps: long = 0;
        for k in h + 1..j {
            ix: long = fn.firstInstr + k;
            o: IROp = p.code[ix].op;
            if (o == IROp.Nop || k == t) { continue; }
            if (o == IROp.Label) {
                // Entered only through its header.
                if (self.namedOutside(p, fn, p.code[ix].name, h, j)) { return false; }
                continue;
            }
            if (!(o == IROp.Const || o == IROp.Mov || o == IROp.Add || o == IROp.Sub || o == IROp.Mul
                  || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor || o == IROp.Shl || o == IROp.Shr
                  || o == IROp.BNot || o == IROp.Convert || isCompare(o))) { return false; }
            d: Temp = p.code[ix].dst;
            if (d == NO_TEMP) { return false; }
            if (!test.bIsImm && d == test.b) { return false; }
            if (d == ctr) {
                in: Instr = p.code.get(ix);
                if (in.op != IROp.Add || in.a != ctr || in.kind != test.kind) { return false; }
                if (!(in.bIsImm && in.bImm == 1) && !self.isOne(p, fn, in.b)) { return false; }
                steps = steps + 1;
            }
            if (self.usesWithin(p, fn, d, h, j) != self.useCount(d)) { return false; }
        }
        // The counter is one of the values checked above: nothing after the loop reads it.
        if (steps != 1) { return false; }
        for k in h + 1..j + 1 { p.code.set(fn.firstInstr + k, instr(IROp.Nop)); }
        jmp: Instr = instr(IROp.Jmp);
        jmp.name = test.name;
        p.code.set(fn.firstInstr + t, jmp);
        self.nJumps = self.nJumps + 1;
        return true;
    }

    // Whether a branch outside instructions `h..j` names label `l`.
    namedOutside &self inout p:IRProgram fn:IRFunc l:Sym h:long j:long -> bool {
        for k in 0..fn.instrCount {
            if (k >= h && k <= j) { continue; }
            ix: long = fn.firstInstr + k;
            o: IROp = p.code[ix].op;
            if ((isBranch(o) || o == IROp.FaultEdge || o == IROp.RecoverPush) && p.code[ix].name == l) { return true; }
        }
        return false;
    }

    // How many reads of `t` instructions `h..j` make.
    usesWithin &self inout p:IRProgram fn:IRFunc t:Temp h:long j:long -> long {
        c: long = 0;
        for k in h..j + 1 {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Nop) { continue; }
            if (in.a == t) { c = c + 1; }
            if (!in.bIsImm && in.b == t) { c = c + 1; }
            if (in.x == t) { c = c + 1; }
            for a in 0..in.argCount { if (p.args.get(in.firstArg + a) == t) { c = c + 1; } }
            for a in 0..in.pieceCount { if (p.asmVals.get(in.firstPiece + a) == t) { c = c + 1; } }
        }
        return c;
    }

    // `t` is written once, by the constant 1.
    isOne &self inout p:IRProgram fn:IRFunc t:Temp -> bool {
        i: long = t - self.base;
        if (t == NO_TEMP || i < 0 || i >= self.defs.len() || self.defs.get(i) != 1) { return false; }
        d: long = self.defAt.get(i);
        return d >= 0 && p.code[fn.firstInstr + d].op == IROp.Const && p.code[fn.firstInstr + d].imm == 1;
    }

    // Whether some `Jz` reads the comparison just before it (past deleted ones): what
    // `fuseBranches` looks for.
    compareThenBranch &self inout p:IRProgram fn:IRFunc -> bool {
        prev: long = -1;
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            o: IROp = p.code[at].op;
            if (o == IROp.Nop) { continue; }
            if (o == IROp.Jz && prev >= 0 && isCompare(p.code[prev].op) && p.code[prev].dst == p.code[at].a) { return true; }
            prev = at;
        }
        return false;
    }

    // ─── use and def counts ──────────────────────────────────────────────────

    // Every temp of this function, counted. `defAt` holds the defining instruction's index when
    // there is exactly one, which is what lets a rewrite reach back to it.
    countUses &self inout p:IRProgram fn:IRFunc -> void {
        n: long = fn.tempCount - self.base;
        if (n < 0) { n = 0; }
        // Overwritten in place and grown only past what an earlier function needed: this runs
        // once per round of three passes, and a write is cheaper than a push.
        resetLongs(&self.uses, n, 0);
        resetLongs(&self.defs, n, 0);
        resetLongs(&self.defAt, n, -1);
        // Read in place: copying each 136-byte instruction out, once per round, was most of this.
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            self.noteUse(p.code[ix].a);
            if (!p.code[ix].bIsImm) { self.noteUse(p.code[ix].b); }
            na: long = p.code[ix].argCount;
            if (na > 0) {
                fa: long = p.code[ix].firstArg;
                for k in 0..na { self.noteUse(p.args.get(fa + k)); }
            }
            np: long = p.code[ix].pieceCount;
            if (np > 0) {
                fp: long = p.code[ix].firstPiece;
                for k in 0..np { self.noteUse(p.asmVals.get(fp + k)); }
            }
            dt: Temp = p.code[ix].dst;
            d: long = dt - self.base;
            if (dt != NO_TEMP && d >= 0 && d < self.defs.len()) {
                self.defs.set(d, self.defs.get(d) + 1);
                self.defAt.set(d, i);
            }
        }
    }

    noteUse &self t:Temp -> void {
        i: long = t - self.base;
        if (t == NO_TEMP || i < 0 || i >= self.uses.len()) { return; }
        self.uses.set(i, self.uses.get(i) + 1);
    }

    useCount &self t:Temp -> long {
        i: long = t - self.base;
        if (t == NO_TEMP || i < 0 || i >= self.uses.len()) { return 2; }   // unknown: assume many
        return self.uses.get(i);
    }
    defCount &self t:Temp -> long {
        i: long = t - self.base;
        if (t == NO_TEMP || i < 0 || i >= self.defs.len()) { return 2; }
        return self.defs.get(i);
    }

    // ─── 1. a local in a register ────────────────────────────────────────────

    // A named scalar slot becomes a temp, so the value can live in a register across a loop.
    //
    // One temp for the whole variable, not one per assignment: this is not SSA, and it does not
    // need to be. The allocator builds a live range from real liveness over the CFG, so a temp
    // with many definitions gets one interval spanning them, which is exactly what a variable
    // is. A `Load` becomes a copy out of that temp and a `Store` a copy into it, and
    // `propagateCopies` then removes most of them.
    //
    // It is refused for anything the slot's address could reach: a name whose address is taken,
    // a global, a name an `asm` block spells, and anything that is not a scalar. An aggregate
    // lives in memory by definition, and is reached through pointers this pass cannot see.
    promoteLocals &self inout p:IRProgram fn:IRFunc -> void {
        // A `recover` handler reads its function's variables after a `raise` from the middle of a
        // call, in whatever state that call left them. In their slots they are exactly that; as
        // temps, an assignment the handler never sees completed could have taken over the
        // register of the value it does need. Such a function keeps its variables in memory.
        if (hasRecover(p, fn)) { return; }
        // `clear` walks the whole table, which the largest function so far has grown: a map that
        // big is replaced instead, or every function after it pays for that one.
        if (self.pinned.cap() > 512) { self.pinned = map![]; } else { self.pinned.clear(); }
        if (self.slotTemp.cap() > 512) { self.slotTemp = map![]; } else { self.slotTemp.clear(); }
        for i in 0..fn.instrCount {
            o0: IROp = p.code[fn.firstInstr + i].op;
            if (o0 != IROp.AddrOf && o0 != IROp.ArrLoad && o0 != IROp.ArrStore && o0 != IROp.Asm
                && o0 != IROp.Load && o0 != IROp.Store) { continue; }
            in: Instr = p.code.get(fn.firstInstr + i);
            // The address of a slot escapes into a pointer nothing here tracks.
            if (in.op == IROp.AddrOf && in.name != NO_SYM) { self.pinned.put(in.name as long, true); }
            // An array element is reached by index, not by name.
            if (in.op == IROp.ArrLoad || in.op == IROp.ArrStore) {
                if (in.name != NO_SYM) { self.pinned.put(in.name as long, true); }
            }
            // A name spelled inside inline assembly is read as a slot, whatever this pass thinks;
            // all but a block's one output of a whole word (`asmOutName`), which goes to the
            // variable's temp instead, the block then defining it.
            if (in.op == IROp.Asm) {
                one: Sym = asmOutName(p, fn, in);
                for k in 0..in.pieceCount {
                    nm: Sym = p.asmNames.get(in.firstPiece + k);
                    if (nm != NO_SYM && nm != one) { self.pinned.put(nm as long, true); }
                }
            }
            if (in.op != IROp.Load && in.op != IROp.Store) { continue; }
            if (in.isGlobal || in.name == NO_SYM) {
                if (in.name != NO_SYM) { self.pinned.put(in.name as long, true); }
                continue;
            }
            // An aggregate's slot is the value; a scalar's slot merely holds one, and so does a
            // backed enum's or a distinct type's (`namedScalar`): an integer, kept in a register
            // like the base it is. So does a `str`, slice or trait-object parameter's: it holds
            // the address of the caller's pair (`lower.k` `noteByRef`), a word, and every access
            // to the parameter reads that word out of it first.
            if ((isAggregate(in.kind) && !namedScalar(in.kind, in.structName) && !fatSeed(in)) || in.kind == Lit.Void) {
                self.pinned.put(in.name as long, true);
            }
        }

        // A parameter's seed load is its definition (the value is still in its argument register
        // when the function starts) so promoting the name has to keep that load, not replace it.
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            if (p.code[at].op == IROp.Asm) {
                in0: Instr = p.code.get(at);
                one: Sym = asmOutName(p, fn, in0);
                if (one == NO_SYM || self.pinned.has(one as long)) { continue; }
                t0: Temp = self.tempFor(p, fn, one);
                if (t0 == NO_TEMP) { continue; }
                for k in 0..in0.pieceCount {
                    if (p.asmNames.get(in0.firstPiece + k) == one) { p.asmNames.set(in0.firstPiece + k, NO_SYM); }
                }
                in0.dst = t0;
                in0.kind = p.kindOf(t0);
                p.code.set(at, in0);
                continue;
            }
            if (p.code[at].op != IROp.Load && p.code[at].op != IROp.Store) { continue; }
            in: Instr = p.code.get(at);
            if (in.name == NO_SYM || self.pinned.has(in.name as long)) { continue; }
            // A parameter's seed is not a load of a value the body stored. It is where the
            // argument enters the function, and the prologue counts the leading run of them to
            // know which registers to drain. Rewritten, it would leave the prologue counting no
            // seeds, and no parameter would be stored anywhere at all. So the seed stays a
            // `Load`, its own dst becomes the variable's temp, and the emitter fills it from the
            // slot once.
            if (in.paramSeed) {
                if (in.dst == NO_TEMP) { continue; }
                if (self.slotTemp.has(in.name as long)) { continue; }
                self.slotTemp.put(in.name as long, in.dst);
                self.nPromoted = self.nPromoted + 1;
                in.promoted = true;
                p.code.set(at, in);
                continue;
            }
            t: Temp = self.tempFor(p, fn, in.name);
            if (t == NO_TEMP) { continue; }
            if (in.op == IROp.Load) {
                // dst = <var>  ->  dst = t
                mv: Instr = instr(IROp.Mov);
                mv.dst = in.dst; mv.a = t; mv.kind = in.kind;
                mv.structName = in.structName;
                // A promoted parameter keeps the seed: the allocator reads it as the temp's
                // first definition, and without it the range starts at the first use.
                mv.paramSeed = in.paramSeed;
                p.code.set(at, mv);
            } else {
                // <var> = a  ->  t = a. A value that need not fit the variable's type (an `int`
                // stored in a `u8`, since a declaration takes any integer) is narrowed to it, just
                // as a store to the slot narrowed it by its width: a register holds its type's
                // canonical word.
                if (narrowsInto(p.kindOf(in.a), in.kind)) {
                    cv: Instr = instr(IROp.Convert);
                    cv.dst = t; cv.a = in.a; cv.kind = in.kind;
                    cv.fromKind = p.kindOf(in.a); cv.toKind = in.kind;
                    p.code.set(at, cv);
                    continue;
                }
                mv: Instr = instr(IROp.Mov);
                mv.dst = t; mv.a = in.a; mv.kind = in.kind;
                mv.structName = in.structName;
                p.code.set(at, mv);
            }
        }
    }

    // The temp standing in for a named slot: the one the lowerer reserved for it, inside this
    // function's own temp range. NO_TEMP when there is none, and then the name stays a slot.
    tempFor &self inout p:IRProgram fn:IRFunc name:Sym -> Temp {
        hit: Option<Temp> = self.slotTemp.find(name as long);
        match hit { Some(t) { return t; } None { } }
        for k in 0..fn.promoCount {
            if (p.promoName.get(fn.firstPromo + k) == name) {
                t: Temp = p.promoTemp.get(fn.firstPromo + k);
                self.slotTemp.put(name as long, t);
                self.nPromoted = self.nPromoted + 1;
                return t;
            }
        }
        return NO_TEMP;
    }

    // ─── 2. copies ───────────────────────────────────────────────────────────

    // `d = Mov s`: every later read of `d` in the block reads `s` instead, provided neither is
    // written between the copy and the read. Within one basic block only: across a branch the
    // question is which definition reaches, and that is what SSA is for.
    //
    // One walk reaches the fixpoint, so there is no second one to confirm it (and no use counts:
    // the walk reads none). A copy is recorded with its source already rewritten, so a chain
    // `b = mov a; c = mov b` reads `a` at once, and a source that was itself a copy still in
    // force would have been rewritten to that copy's source. The walk deletes only `d = mov d`,
    // and does so before it counts that write, so a second walk would see the same writes and
    // the same copies.
    propagateCopies &self inout p:IRProgram fn:IRFunc -> void {
        self.copyRound(p, fn);
    }

    // The walk. Within a block, `d = mov s` makes every later read of d a read of s, until either
    // is written again: each temp's writes in the block are counted, and a copy remembers the
    // count its source had. That is one walk for all the copies rather than a walk to the end
    // of the block for each, which matters because inlined code makes long blocks with many
    // copies. A call is not a barrier, since a temp survives one (the
    // allocator gives it a callee-saved register or a slot). A label or a terminator ends the
    // block, after the terminator's own operands are rewritten.
    copyRound &self inout p:IRProgram fn:IRFunc -> long {
        n: long = fn.tempCount - self.base;
        if (n < 0) { n = 0; }
        growLongs(&self.cpStamp, n);
        growLongs(&self.cpTo, n);
        growLongs(&self.cpVer, n);
        growLongs(&self.vStamp, n);
        growLongs(&self.vCount, n);
        // Stamps continue from the last walk, so nothing has to be cleared between them.
        blk: long = self.blkSeq + 1;
        changed: long = 0;
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            o: IROp = p.code[at].op;
            if (o == IROp.Nop) { continue; }
            if (o == IROp.Label) { blk = blk + 1; continue; }
            in: Instr = p.code.get(at);
            here: bool = false;
            na: Temp = self.copyOf(in.a, blk);
            if (na != in.a) { in.a = na; here = true; }
            if (!in.bIsImm) {
                nb: Temp = self.copyOf(in.b, blk);
                if (nb != in.b) { in.b = nb; here = true; }
            }
            for k in 0..in.argCount {
                t: Temp = p.args.get(in.firstArg + k);
                nt: Temp = self.copyOf(t, blk);
                if (nt != t) { p.args.set(in.firstArg + k, nt); changed = changed + 1; }
            }
            for k in 0..in.pieceCount {
                t: Temp = p.asmVals.get(in.firstPiece + k);
                nt: Temp = self.copyOf(t, blk);
                if (nt != t) { p.asmVals.set(in.firstPiece + k, nt); changed = changed + 1; }
            }
            if (in.op == IROp.Mov && in.dst != NO_TEMP && in.dst == in.a) {
                p.code.set(at, instr(IROp.Nop));
                changed = changed + 1;
                continue;
            }
            if (here) { p.code.set(at, in); changed = changed + 1; }
            d: long = in.dst - self.base;
            if (in.dst != NO_TEMP && d >= 0 && d < n) {
                if (self.vStamp.get(d) != blk) { self.vStamp.set(d, blk); self.vCount.set(d, 0); }
                self.vCount.set(d, self.vCount.get(d) + 1);
                // A copy stands for its source in the rest of this block, whatever else writes
                // the destination elsewhere: a read here is reached by this write alone. Any other
                // write of it here ends that.
                s: long = in.a - self.base;
                if (in.op == IROp.Mov && in.a != NO_TEMP && s >= 0 && s < n) {
                    self.cpStamp.set(d, blk);
                    self.cpTo.set(d, in.a);
                    self.cpVer.set(d, self.versionOf(s, blk));
                } else {
                    self.cpStamp.set(d, 0);
                }
            }
            if (isTerminator(o)) { blk = blk + 1; }
        }
        self.blkSeq = blk;
        self.nCopies = self.nCopies + changed;
        return changed;
    }

    // What `t` reads as here: the source of the copy that made it, while that is unchanged.
    copyOf &self t:Temp blk:long -> Temp {
        r: long = t - self.base;
        if (t == NO_TEMP || r < 0 || r >= self.cpStamp.len() || self.cpStamp.get(r) != blk) { return t; }
        s: Temp = self.cpTo.get(r);
        if (self.versionOf(s - self.base, blk) != self.cpVer.get(r)) { return t; }
        return s;
    }

    versionOf &self r:long blk:long -> long {
        if (self.vStamp.get(r) != blk) { return 0; }
        return self.vCount.get(r);
    }

    // `t = <something>` immediately followed by `Mov d, t`, where nothing else ever reads `t`:
    // the something writes `d` directly and the copy goes.
    //
    // This is what `propagateCopies` cannot do. There the copy's destination is the variable's
    // temp, which has a definition per assignment, so no read of it can be rewritten. Here the
    // copy's source is the single-use temp, and moving the write forward is always safe when the
    // two instructions are adjacent (deleted ones between them do nothing): nothing can come
    // between them to observe either. `n = n / 2` is then one instruction writing `n`, where the
    // quotient went into a register of its own and was copied over.
    //
    // One walk is the fixpoint. A rewrite deletes the copy and moves its destination onto the
    // instruction before it, which is still there, so no two instructions become adjacent that
    // were not; and it removes the copy's source entirely, so no other temp's counts change. A
    // chain `t = op; u = mov t; d = mov u` collapses in the one walk, front to back.
    coalesceMoves &self inout p:IRProgram fn:IRFunc -> void {
        self.countUses(p, fn);
        self.coalesceRound(p, fn);
    }

    // The walk, with the counts as they stand. A count taken before deletions is no smaller than
    // the true one, so a count of one is still exactly one (the copy that reads the temp is
    // there); and a rewrite here changes the counts of its own copy's source alone, which nothing
    // else reads.
    coalesceRound &self inout p:IRProgram fn:IRFunc -> long {
        changed: long = 0;
        for i in 1..fn.instrCount {
            at: long = fn.firstInstr + i;
            if (p.code[at].op != IROp.Mov) { continue; }
            mv: Instr = p.code.get(at);
            if (mv.op != IROp.Mov || mv.dst == NO_TEMP || mv.a == NO_TEMP) { continue; }
            // The instruction before the copy, past any deleted ones (an inlined body's jump to
            // its end label leaves one between the value it returns and the copy out).
            j: long = at - 1;
            while (j > fn.firstInstr && p.code[j].op == IROp.Nop) { j = j - 1; }
            def: Instr = p.code.get(j);
            if (def.dst != mv.a || !coalescible(def.op) || def.paramSeed) { continue; }
            if (self.useCount(mv.a) != 1 || self.defCount(mv.a) != 1) { continue; }
            def.dst = mv.dst;
            p.code.set(j, def);
            p.code.set(at, instr(IROp.Nop));
            self.nCopies = self.nCopies + 1;
            changed = changed + 1;
        }
        return changed;
    }

    // ─── 3. immediates ───────────────────────────────────────────────────────

    // A `Const` read exactly once, as the right operand of something that encodes one, stops
    // being a register: the constant rides on the instruction and the `Const` becomes dead.
    selectImmediates &self inout p:IRProgram fn:IRFunc -> void {
        self.countUses(p, fn);
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            // A comparison with its constant on the left (`4 <= n`, which folding a length and
            // inlining leave behind) is turned round, so the constant is the operand that can be
            // an immediate.
            o: IROp = p.code[at].op;
            if ((o == IROp.Jcc || isCompare(o)) && !p.code[at].bIsImm && p.code[at].a != NO_TEMP && p.code[at].b != NO_TEMP) {
                self.constRight(p, fn, at);
            }
            if (p.code[at].bIsImm || p.code[at].b == NO_TEMP || !takesImmediate(p.code[at].op)) { continue; }
            in: Instr = p.code.get(at);
            // A float's operand goes to an `xmm` register, which no instruction loads an
            // immediate into.
            if (in.kind == Lit.Float || in.kind == Lit.Double) { continue; }
            if (self.useCount(in.b) != 1 || self.defCount(in.b) != 1) { continue; }
            d: long = self.defAt.get(in.b - self.base);
            if (d < 0) { continue; }
            src: Instr = p.code.get(fn.firstInstr + d);
            if (src.op != IROp.Const) { continue; }
            if (src.imm < IMM_MIN || src.imm > IMM_MAX) { continue; }
            in.bIsImm = true;
            in.bImm = src.imm;
            in.b = NO_TEMP;
            p.code.set(at, in);
            p.code.set(fn.firstInstr + d, instr(IROp.Nop));
            self.nImm = self.nImm + 1;
        }
    }

    // `c op t` with `c` a constant becomes `t op' c` (`swapCompare`): the same test.
    constRight &self inout p:IRProgram fn:IRFunc at:long -> void {
        in: Instr = p.code.get(at);
        if (in.kind == Lit.Float || in.kind == Lit.Double) { return; }
        if (!self.constDef(p, fn, in.a) || self.constDef(p, fn, in.b)) { return; }
        t: Temp = in.a;
        in.a = in.b;
        in.b = t;
        if (in.op == IROp.Jcc) { in.cmpOp = swapCompare(in.cmpOp); } else { in.op = swapCompare(in.op); }
        p.code.set(at, in);
    }

    // `t` has one definition in this function, and it is a `Const`.
    constDef &self inout p:IRProgram fn:IRFunc t:Temp -> bool {
        if (t == NO_TEMP || t < self.base || self.defCount(t) != 1) { return false; }
        d: long = self.defAt.get(t - self.base);
        if (d < 0) { return false; }
        return p.code[fn.firstInstr + d].op == IROp.Const;
    }

    // ─── 4. compare and branch, as one ───────────────────────────────────────

    // `CmpLt t, a, b` immediately followed by `Jz L, t` is a branch on the comparison, spelled in
    // five instructions: the compare, a `setcc`, a widening, and then a second compare against
    // zero. Fused it is one compare and one conditional jump.
    //
    // `Jz` jumps when the value is zero (when the comparison did not hold), so the fused branch
    // carries the negated comparison. This is done only when the comparison sits immediately
    // before the branch and its result is read nowhere else: anything between them could set the
    // flags, and a second reader still needs the 0/1.
    fuseBranches &self inout p:IRProgram fn:IRFunc -> void {
        // The counts `selectImmediates` just took: it changes only how constants are read, never
        // how often a comparison's result is.
        i: long = 0;
        end: long = fn.firstInstr + fn.instrCount;
        while (i + 1 < fn.instrCount) {
            at: long = fn.firstInstr + i;
            i = i + 1;
            if (!isCompare(p.code[at].op)) { continue; }
            // A deleted instruction between them emits nothing, so it leaves the flags alone.
            nx: long = at + 1;
            while (nx < end && p.code[nx].op == IROp.Nop) { nx = nx + 1; }
            if (nx >= end || p.code[nx].op != IROp.Jz) { continue; }
            c: Instr = p.code.get(at);
            j: Instr = p.code.get(nx);
            if (c.dst == NO_TEMP || j.a != c.dst) { continue; }
            if (self.useCount(c.dst) != 1) { continue; }
            fused: Instr = instr(IROp.Jcc);
            fused.a = c.a;
            fused.b = c.b;
            fused.bIsImm = c.bIsImm;
            fused.bImm = c.bImm;
            fused.cmpOp = negateCompare(c.op);
            // Over floats the negated comparison is not the opposite one (both are false on a
            // NaN), so a float branch keeps the comparison and says it jumps when it does NOT
            // hold (`imm` 1), which the emitter spells as the inverted condition codes.
            if (c.kind == Lit.Float || c.kind == Lit.Double) { fused.cmpOp = c.op; fused.imm = 1; }
            fused.kind = c.kind;                 // signedness comes from the comparison's type
            fused.name = j.name;
            p.code.set(at, instr(IROp.Nop));
            p.code.set(nx, fused);
            self.nFused = self.nFused + 1;
        }
    }

    // ─── branches on constants ───────────────────────────────────────────────

    // `if (atCompileTime()) { ... }` and any other test of a value fixed when the program is
    // compiled: a `Jz` on a temp whose one definition is a constant always goes the same way, so
    // it becomes a `Jmp` (the constant is zero) or nothing. Done before inlining, so the code the
    // test guarded is gone when the inliner weighs a body (`memcpy`'s compile-time loop would
    // otherwise keep the body from being copied anywhere). `flow.k` decides such branches again
    // after inlining, with everything else it knows. Answers whether a branch was decided.
    foldConstBranches &self inout p:IRProgram fn:IRFunc -> bool {
        self.countUses(p, fn);
        folded: bool = false;
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            // A fused compare and branch of two constants (`--no-refold` leaves it): taken when
            // the comparison holds, so it is a `Jz` on the comparison's negation.
            if (p.code[at].op == IROp.Jcc && !gRefoldOff) {
                c: Instr = p.code.get(at);
                if (c.kind == Lit.Float || c.kind == Lit.Double || !self.constDef(p, fn, c.a)) { continue; }
                y: long = c.bImm;
                if (!c.bIsImm) {
                    if (!self.constDef(p, fn, c.b)) { continue; }
                    db: long = self.defAt.get(c.b - self.base);
                    y = p.code[fn.firstInstr + db].imm;
                }
                da: long = self.defAt.get(c.a - self.base);
                x: long = p.code[fn.firstInstr + da].imm;
                if (constCompare(c.cmpOp, c.kind, x, y)) {
                    j: Instr = instr(IROp.Jmp);
                    j.name = c.name;
                    p.code.set(at, j);
                } else { p.code.set(at, instr(IROp.Nop)); }
                self.nJumps = self.nJumps + 1;
                folded = true;
                continue;
            }
            if (p.code[at].op != IROp.Jz || !self.constDef(p, fn, p.code[at].a)) { continue; }
            d: long = self.defAt.get(p.code[at].a - self.base);
            v: long = p.code[fn.firstInstr + d].imm;
            if (v == 0) {
                j: Instr = instr(IROp.Jmp);
                j.name = p.code[at].name;
                p.code.set(at, j);
            } else { p.code.set(at, instr(IROp.Nop)); }
            self.nJumps = self.nJumps + 1;
            folded = true;
        }
        return folded;
    }

    // Every instruction no path from the entry reaches, deleted: what a decided branch cut off,
    // labels and loops included, which `simplifyJumps` alone leaves behind (it stops at the first
    // label, and a dead loop's labels are named by its own jumps). A walk over the instructions:
    // a jump goes on at its label, a conditional one at both, and a return, an unconditional jump
    // or a call that never returns ends the path.
    dropUnreachable &self inout p:IRProgram fn:IRFunc -> void {
        n: long = fn.instrCount;
        labels: HashMap<long, long>;
        for i in 0..n {
            if (p.code[fn.firstInstr + i].op == IROp.Label) { labels.put(p.code[fn.firstInstr + i].name as long, i); }
        }
        seen: Vec<bool>;
        for i in 0..n { seen.push(false); }
        work: Vec<long>;
        work.push(0);
        while (work.len() > 0) {
            i: long = work.pop();
            while (i < n && !seen.get(i)) {
                seen.set(i, true);
                o: IROp = p.code[fn.firstInstr + i].op;
                // A `recover` handler is reached by the fault edges of its body's calls.
                if (isBranch(o) || o == IROp.FaultEdge) {
                    hit: Option<long> = labels.find(p.code[fn.firstInstr + i].name as long);
                    match hit { Some(t) { work.push(t); } None { } }
                }
                if (endsFlow(o) || (o == IROp.Call && p.code[fn.firstInstr + i].noReturn)) { i = n; }
                else { i = i + 1; }
            }
        }
        for i in 0..n {
            if (!seen.get(i) && p.code[fn.firstInstr + i].op != IROp.Nop) {
                p.code.set(fn.firstInstr + i, instr(IROp.Nop));
                self.nJumps = self.nJumps + 1;
            }
        }
    }

    // ─── 5. jumps ────────────────────────────────────────────────────────────

    // A `Jmp` whose target is the next thing in the stream, and everything between a terminator
    // and the next label, which nothing can reach.
    simplifyJumps &self inout p:IRProgram fn:IRFunc -> void {
        i: long = 0;
        while (i < fn.instrCount) {
            at: long = fn.firstInstr + i;
            o1: IROp = p.code[at].op;
            i = i + 1;
            if (o1 == IROp.Jmp) {
                if (self.nextLabelIs(p, fn, i, p.code[at].name)) {
                    p.code.set(at, instr(IROp.Nop));
                    self.nJumps = self.nJumps + 1;
                }
                continue;
            }
            // A branch to where control goes anyway decides nothing.
            if (!gEmptyLoopsOff && (o1 == IROp.Jcc || o1 == IROp.Jz) && self.nextLabelIs(p, fn, i, p.code[at].name)) {
                p.code.set(at, instr(IROp.Nop));
                self.nJumps = self.nJumps + 1;
                continue;
            }
            if ((o1 == IROp.Jcc && !isFloat(p.code[at].kind)) || o1 == IROp.Jz) {
                self.branchOverJump(p, fn, at, i);
                continue;
            }
            // Only an unconditional exit ends the stream. `isTerminator` says yes to `Jz` and
            // `Jcc` too, and control falls through both when the condition does not hold. Using
            // it here would delete every loop body, since the top of a `while` is a fused branch.
            if (!endsFlow(o1) && !(o1 == IROp.Call && p.code[at].noReturn)) { continue; }
            // Unreachable until a label gives the stream a way back in.
            k: long = i;
            while (k < fn.instrCount) {
                nxo: IROp = p.code[fn.firstInstr + k].op;
                if (nxo == IROp.Label) { k = fn.instrCount; continue; }
                if (nxo != IROp.Nop) {
                    p.code.set(fn.firstInstr + k, instr(IROp.Nop));
                    self.nJumps = self.nJumps + 1;
                }
                k = k + 1;
            }
        }
    }

    // A label no branch names: control only falls into it, so it starts no block, and the
    // block-local passes (copies, addresses, constants) see across where it stood. An inlined
    // body's end label is the common one, once its last `ret`'s jump is gone.
    dropUnusedLabels &self inout p:IRProgram fn:IRFunc -> void {
        if (self.named.cap() > 512) { self.named = map![]; } else { self.named.clear(); }
        for i in 0..fn.instrCount {
            o: IROp = p.code[fn.firstInstr + i].op;
            // A `recover` handler's label is where a `raise` resumes (`RecoverPush` takes its address).
            named: bool = isBranch(o) || o == IROp.FaultEdge || o == IROp.RecoverPush;
            if (named && p.code[fn.firstInstr + i].name != NO_SYM) { self.named.put(p.code[fn.firstInstr + i].name as long, true); }
        }
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            if (p.code[at].op != IROp.Label || self.named.has(p.code[at].name as long)) { continue; }
            p.code.set(at, instr(IROp.Nop));
            self.nJumps = self.nJumps + 1;
        }
    }

    // `if (c) goto L1; goto L2; L1:` is `if (!c) goto L2; L1:`: the same two ways out, and one
    // jump fewer where control went on to L2. The branch at `at` (an integer comparison's, or a
    // test against zero; a float comparison and its negation are both false of a NaN) is turned
    // round onto the jump's target and the jump goes. `L1` stays for whatever else names it.
    branchOverJump &self inout p:IRProgram fn:IRFunc at:long i:long -> void {
        j: long = i;
        while (j < fn.instrCount && p.code[fn.firstInstr + j].op == IROp.Nop) { j = j + 1; }
        if (j >= fn.instrCount || p.code[fn.firstInstr + j].op != IROp.Jmp) { return; }
        if (!self.nextLabelIs(p, fn, j + 1, p.code[at].name)) { return; }
        to: Sym = p.code[fn.firstInstr + j].name;
        if (to == p.code[at].name) { return; }
        br: Instr = p.code.get(at);
        if (br.op == IROp.Jz) {
            jc: Instr = instr(IROp.Jcc);
            jc.a = br.a;
            jc.bIsImm = true;
            jc.bImm = 0;
            jc.kind = p.kindOf(br.a);
            jc.cmpOp = IROp.CmpNe;
            br = jc;
        } else {
            br.cmpOp = negateCompare(br.cmpOp);
        }
        br.name = to;
        p.code.set(at, br);
        p.code.set(fn.firstInstr + j, instr(IROp.Nop));
        self.nJumps = self.nJumps + 1;
    }

    // Whether the next real instruction from `i` is the label `name`.
    nextLabelIs &self inout p:IRProgram fn:IRFunc i:long name:Sym -> bool {
        for k in i..fn.instrCount {
            ko: IROp = p.code[fn.firstInstr + k].op;
            if (ko == IROp.Nop) { continue; }
            if (ko != IROp.Label) { return false; }
            if (p.code[fn.firstInstr + k].name == name) { return true; }
            // A run of labels: any of them being the target still means the jump goes nowhere.
        }
        return false;
    }

    // ─── 6. results nobody reads ─────────────────────────────────────────────

    // An instruction whose destination is never read and which does nothing else. A call is not
    // one of these however unused its result: it is what the program was for. One count, then a
    // walk that takes each dead instruction and, with it, every definition it was the last reader
    // of (`dropIfDead`), rather than a count and a walk per layer of the chain.
    dropDeadDefs &self inout p:IRProgram fn:IRFunc -> void {
        dead: long = self.nDead;
        self.countUses(p, fn);
        again: bool = true;
        rounds: long = 0;
        while (again && rounds < MAX_ROUNDS) {
            self.ddAgain = false;
            for i in 0..fn.instrCount { self.dropIfDead(p, fn, i); }
            again = self.ddAgain;
            rounds = rounds + 1;
        }
        // What `runOne` asks next reads the counts as they now stand (`coalesceRound`).
        if (self.nDead > dead) { self.countUses(p, fn); }
    }

    // Instruction `i` goes when its result is read nowhere and it does nothing else; then so does
    // the one definition of each operand it was the last reader of, and so on up the chain. A
    // temp with several definitions left unread is found by one more walk.
    dropIfDead &self inout p:IRProgram fn:IRFunc i0:long -> void {
        self.ddStack.clear();
        self.ddStack.push(i0);
        while (self.ddStack.len() > 0) {
            i: long = self.ddStack.pop();
            at: long = fn.firstInstr + i;
            dt: Temp = p.code[at].dst;
            if (dt == NO_TEMP || !pureResult(p.code[at].op)) { continue; }
            if (self.useCount(dt) != 0) { continue; }
            // A promoted parameter's seed holds a register; deleting it frees the allocator
            // to put something else there before the value has been read.
            if (p.code[at].paramSeed) { continue; }
            in: Instr = p.code.get(at);
            p.code.set(at, instr(IROp.Nop));
            self.nDead = self.nDead + 1;
            self.ddRead(in.a);
            if (!in.bIsImm) { self.ddRead(in.b); }
            for k in 0..in.argCount { self.ddRead(p.args.get(in.firstArg + k)); }
            for k in 0..in.pieceCount { self.ddRead(p.asmVals.get(in.firstPiece + k)); }
        }
    }

    // A read of `t` gone: one fewer, and its definition may be dead now.
    ddRead &self t:Temp -> void {
        r: long = t - self.base;
        if (t == NO_TEMP || r < 0 || r >= self.uses.len()) { return; }
        u: long = self.uses.get(r) - 1;
        self.uses.set(r, u);
        if (u != 0) { return; }
        if (self.defs.get(r) == 1) { self.ddStack.push(self.defAt.get(r)); } else { self.ddAgain = true; }
    }
}

// `v` as `n` copies of `x`.
local resetLongs inout v:Vec<long> n:long x:long -> void {
    if (v.len() > n) { v.truncate(n); }
    for i in 0..v.len() { v.set(i, x); }
    while (v.len() < n) { v.push(x); }
}

// Control cannot fall past this instruction. A conditional branch is not one: it is a
// terminator (it ends a basic block) but the next instruction still runs when it is not taken.
pub endsFlow op:IROp -> bool {
    return op == IROp.Jmp || op == IROp.Ret || op == IROp.RetVoid;
}

// Whether this operation encodes a 32-bit immediate as its right operand on x86-64. Division does
// not (`idiv` takes only a register or memory) and neither does anything that is not arithmetic.
// The seed of a `str`, slice or trait-object parameter, whose slot holds the caller's address.
local fatSeed in:Instr -> bool {
    return in.op == IROp.Load && in.paramSeed && (in.kind == Lit.Str || in.kind == Lit.Slice || in.kind == Lit.TraitObj);
}

pub takesImmediate op:IROp -> bool {
    return op == IROp.Add || op == IROp.Sub || op == IROp.Mul
        || op == IROp.BAnd || op == IROp.BOr || op == IROp.BXor
        || op == IROp.Shl || op == IROp.Shr
        // A fused compare-and-branch encodes one too, and the lowerer makes those before this
        // pass runs. Without it, `while (i < 1000000)` comes out as a constant moved into a
        // register and then compared, which is the shape immediates exist to remove.
        || op == IROp.Jcc
        || isCompare(op);
}

// What `coalesceMoves` may retarget: an instruction whose only effect on the registers is its
// destination's value. A division may fault, but it faults the same whichever temp it writes.
local coalescible op:IROp -> bool { return pureResult(op) || op == IROp.Div || op == IROp.Mod; }

// Whether an instruction's whole effect is its destination, so removing it when nothing reads
// that removes nothing else. A load from a name is one: the slot is still there afterwards.
// The local an `asm` block's only output goes to, when that output can go straight to the
// local's temp: the block's one named piece, an `out` from a whole 64-bit general register or an
// `xmm` register into a local of this function whose temp (`promoName`) is a word wide and no
// aggregate. NO_SYM otherwise, and the name stays a slot the block writes.
local asmOutName inout p:IRProgram fn:IRFunc in:Instr -> Sym {
    if (gAsmOutOff || in.op != IROp.Asm || in.dst != NO_TEMP) { return NO_SYM; }
    one: Sym = NO_SYM;
    reg: str = "";
    for k in 0..in.pieceCount {
        at: long = in.firstPiece + k;
        nm: Sym = p.asmNames.get(at);
        if (nm == NO_SYM) { continue; }
        if (one != NO_SYM || p.asmKinds.get(at) != AsmKind.Out) { return NO_SYM; }
        one = nm;
        reg = nameOf(p.asmRegs.get(at));
    }
    if (one == NO_SYM || !wholeWordReg(reg)) { return NO_SYM; }
    for k in 0..fn.promoCount {
        if (p.promoName.get(fn.firstPromo + k) != one) { continue; }
        t: Temp = p.promoTemp.get(fn.firstPromo + k);
        kd: Lit = p.kindOf(t);
        if (isAggregate(kd) || widthOf(kd) != 8) { return NO_SYM; }
        return one;
    }
    return NO_SYM;
}

// A register an `out` may name for a whole word: one of the sixteen 64-bit general registers but
// the stack and frame pointers, or an `xmm` register.
local wholeWordReg r:str -> bool {
    if (r.len >= 4 && charAt(r, 0) == 'x' && charAt(r, 1) == 'm' && charAt(r, 2) == 'm') { return true; }
    return r == "rax" || r == "rbx" || r == "rcx" || r == "rdx" || r == "rsi" || r == "rdi"
        || r == "r8" || r == "r9" || r == "r10" || r == "r11" || r == "r12" || r == "r13"
        || r == "r14" || r == "r15";
}

pub pureResult op:IROp -> bool {
    return op == IROp.Const || op == IROp.Mov || op == IROp.Load
        || op == IROp.Add || op == IROp.Sub || op == IROp.Mul
        || op == IROp.BAnd || op == IROp.BOr || op == IROp.BXor
        || op == IROp.Shl || op == IROp.Shr || op == IROp.BNot
        || op == IROp.Convert || op == IROp.AddrOf || op == IROp.StrAddr
        || op == IROp.StrLitVal || op == IROp.AggSlot || op == IROp.VtableAddr
        || op == IROp.FnAddr || op == IROp.ArrLoad || op == IROp.PtrLoad
        || isCompare(op);
}

// `v` at least `n` long; what it holds is left (the readers stamp their entries).
local growLongs inout v:Vec<long> n:long -> void {
    while (v.len() < n) { v.push(0); }
}

// Whether `x op y` holds for two constants compared at `k`: each first cut to the width the
// comparison reads and extended as the kind says, then compared signed or unsigned, as the
// emitter's `cmp` and condition code would.
local constCompare op:IROp k:Lit a:long b:long -> bool {
    ti: TypeInfo = typeInfo(k);
    w: long = ti.size;
    if (w < 1 || w > 8) { w = 8; }
    else if (w == 3) { w = 4; }
    else if (w > 4) { w = 8; }
    x: long = a;
    y: long = b;
    if (w < 8 && ti.unsignedNum) {
        x = a & ((1 << (w * 8)) - 1);
        y = b & ((1 << (w * 8)) - 1);
    } else if (w < 8) {
        sh: long = 64 - w * 8;
        x = (a << sh) >> sh;
        y = (b << sh) >> sh;
    }
    if (op == IROp.CmpEq) { return x == y; }
    if (op == IROp.CmpNe) { return x != y; }
    if (ti.unsignedNum) {
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
