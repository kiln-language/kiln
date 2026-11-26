// The optimizations that look past one basic block: constants, addresses, redundant loads and
// computations, loop-invariant code, and the branches (bounds checks among them) that what is
// already known decides.
//
// `opt.k` works inside one block, or from use counts. This file builds each function's
// control-flow graph and runs a forward dataflow over it to a fixpoint, working out what is known
// on entry to each block. It runs once, after inlining (main.k). By then the accessors a loop
// calls (`Vec.get`, `Vec.set`, `Vec.at`) have been spliced into the loop, so their checks sit
// next to the loop's own condition, where the facts can decide them.
//
// `runOne` does the following to each function, in this order:
//
//   foldConstants    An operation on constants becomes a constant, computed at the operation's
//                    width and signedness exactly as the emitter would. The identities go too
//                    (x+0, x*1, x&0 and the rest), x * 2^k becomes a shift, a read of an
//                    immutable global whose value is known becomes that value, and a branch on
//                    constants becomes a jump or nothing.
//   foldAddresses    [t + o], where t = x + k earlier in the same block, becomes [x + k + o]. That
//                    is one instruction fewer, and two reads of one field through one pointer then
//                    name the same place.
//   shareCopies      d = mov s, with d and s each written once, makes every read of d a read of s.
//   thread           An edge into a block that does nothing but branch, when the edge already
//                    decides the branch, jumps straight to where the branch would go.
//   the dataflow     (`collectFacts`, `solve`) A fact is a relation between a temp and a temp or
//                    a constant, or "this memory location holds this temp", or "this temp holds
//                    `a op b`". A branch establishes a relation on the edge it takes (and its
//                    negation on the other), and a `Bounds` check that passed establishes one
//                    after it. A load or a store establishes a memory fact, and an instruction
//                    computing an expression establishes that expression's fact. A fact holds on
//                    entry to a block when it holds at the end of every edge into it. Writing a
//                    temp ends every fact that names it. A store that may write a location ends
//                    that location's facts, and so does an `asm` block, unless the location is a
//                    frame slot nothing else can reach. A call ends what its callee may write
//                    (`effects.k`), or everything a call can reach when that is not known.
//   ranges           Only when something asks whether a value can be negative (a bounds check, a
//                    division, a comparison with a constant): each temp gets an interval
//                    (`computeRanges`) and a never-negative flag (`computeNonneg`).
//   rewrite          A load whose location's value is known becomes a copy of the temp holding it
//                    (redundant-load elimination and store-to-load forwarding). A computation
//                    whose value some temp already holds becomes a copy of that temp. A branch or
//                    a bounds check the facts decide becomes a jump or nothing. A signed division
//                    or remainder by 2^k of a value that is never negative becomes a shift or a
//                    mask. Whatever that leaves foldable is folded again, and code no path reaches
//                    any more (a removed check's panic, mostly) goes.
//   threadPastSlots  An edge into a join block that only tests a tag its predecessors stored is
//                    threaded past it; when one is, the dataflow and the rewrite run once more.
//   forwardCopies    A block copy of a block copy reads the original source.
//   dropDeadSlots    Writes into a frame slot nothing reads go.
//   hoist            An instruction in a loop whose value is the same on every trip moves to a
//                    preheader, to run once before the loop.
//   forwardResults   An aggregate a call returns is built where it ends up, not copied there.
//
// Then a few of `opt.k`'s passes tidy up what the rewrites left behind: copies to propagate,
// constants to carry as immediates, jumps to nowhere, and dead definitions (`sweep`).
//
// Soundness. A fact is made only by an instruction that makes it true (the edge of a branch, a
// check that passed, a load, a store), and it is dropped at anything that could make it false. A
// block's facts are the ones true on EVERY path into it, and a call that never returns
// (`noReturn`) has no path out. So a removed check is one that could not have failed, and a
// removed load is one whose value was already in hand. Where the pass is unsure it keeps the
// instruction: a location reached through a pointer may be any other such location, any global,
// or any slot whose address was ever handed on, and a sum is trusted not to wrap only when a fact
// bounds it.
#include <{ir, opt, effects}>
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
local F_LREL: long = 3;     // a temp against what a memory location holds: `t op [loc]`

// How a predecessor reaches a block: through the branch at its end, or by falling through.
local E_TAKEN: long = 0;
local E_FALL: long = 1;

// What a location is relative to: a temp's value (any pointer), a frame slot, or a global.
local R_TEMP: long = 0;
local R_SLOT: long = 1;
local R_GLOBAL: long = 2;

// The most instructions a join block may hold for an edge to be threaded past it
// (`threadPastSlots`): a few slot addresses, a block copy, the load.
local MAX_THREAD_BODY: long = 8;

// A function's dataflow is skipped when its bitsets would pass this many bits, which takes
// thousands of blocks and thousands of facts; this compiler has a handful of such functions.
// They still get every other pass.
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
    lent: HashMap<long, bool>,      // slots whose address went only to calls that do not keep it
    callFx: Vec<long>,              // per instruction: a direct call's callee summary (`effects.k`), or -1
    globalAt: HashMap<long, long>,  // a global's name -> its index in the program's tables
    // The globals nothing writes once the program runs: not `var`, and computed by the compiler (an
    // image, or a folded number), so in `.rodata`. What is known of them, and of the blocks their
    // images own, is never ended by a store, a call or `asm`. A flag per name (`isRo`), since it is
    // asked of every global a function reads; `roAny` says whether any is set.
    roGlobals: Vec<bool>, roAny: bool,
    roHere: bool,                   // this function takes the address of one (`runOne`)
    riImage: long, riOff: long,     // what `roImageOf` found
    roSeen: Vec<long>,
    hCall: long,                    // the call `keptOnlyFor` found

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
    // The borrowed parameters (`IRFunc.borrows`): each one's own bytes are written during the call
    // only through temps derived from it or by calls handed one of those (the law of
    // exclusivity). Per temp, the borrowed parameters it may be derived from (`bpMask`, a bit per
    // entry of `bpParam`) and whether it may hold anything else (`bpOther`); per borrowed
    // parameter, the memory facts about its own bytes (`ownSets`, `words` long each), and what a
    // call and a write through a pointer end with all of those left out (`callOther`, `tempOther`).
    fnBorrows: long, fnUnsafe: bool,
    bpParam: Vec<long>, bpMask: Vec<long>, bpOther: Vec<bool>, bpRead: Vec<long>,
    // The borrowed parameters (bits as in `bpMask`) of which the function stores or hands on a
    // derived address where this pass loses track of it (`bpLeaks`). What any call and any pointer
    // of no known origin may reach then includes their bytes.
    bpLeak: long,
    ownSets: Vec<long>, callOther: Vec<long>, tempOther: Vec<long>,
    // For the register heuristic in `rewrite`: each temp's last two reads by position (`rdLast`,
    // `rdPrev`), for each position the last call at or before it (`callAt`), and what `madeAgain`
    // answered of each temp (`madeMemo`: 0 not asked, 1 no, 2 yes).
    rdLast: Vec<long>, rdPrev: Vec<long>, callAt: Vec<long>, madeMemo: Vec<long>,
    // Roots (rk, root) by key, each with its locations as a list (`rootHead`, `locNext`); each
    // location with its memory facts as a list (`locFactHead`, `factNext`).
    rootKey: HashMap<long, long>, rRk: Vec<long>, rRoot: Vec<long>, rootHead: Vec<long>,
    tempRootAt: Vec<long>,   // a temp's root (`R_TEMP`), by the temp: the hash's answer without the hash
    locNext: Vec<long>, locFactHead: Vec<long>, factNext: Vec<long>, keep: Vec<long>,
    words: long, nf: long,
    bits: Vec<long>,
    cur: Vec<long>,
    addOk: Vec<bool>,         // per instruction: its `+`, `*` or `<<` cannot wrap when its operands are never negative
    // Value ranges (`computeRanges`): per temp the signed interval every value it is given lies
    // in, valid when `rOn`; and per instruction what the facts there say of its operands: `a`'s
    // and `b`'s intervals, and a temp `a` is below (`(y << 1) | strict`, or -1).
    rLo: Vec<long>, rHi: Vec<long>, rOn: bool, nLo: Vec<long>, nHi: Vec<long>, rDefs: Vec<long>, rFixed: Vec<bool>,
    oaLo: Vec<long>, oaHi: Vec<long>, obLo: Vec<long>, obHi: Vec<long>, oaUp: Vec<long>,
    condHi: Vec<long>,        // per single-definition temp: its upper bound, on that same condition (`boundWalk`)
    transDepth: long,         // `decide` through a third temp, not twice over
    // Per block copy, its (source fact, destination fact) pairs as a run; and per block whether
    // one is in it.
    cmFirst: Vec<long>, cmCount: Vec<long>, cmSrc: Vec<long>, cmDst: Vec<long>, cmOn: Vec<bool>,
    copies: Vec<long>, copyAt: Vec<long>, needNonneg: bool,
    tStack: Vec<long>, tWritten: Vec<long>, tDefs: Vec<Temp>, tSeen: Vec<bool>,     // `threadPastSlots`
    bDyn: Vec<bool>,
    // Jump threading: each edge's decision into the block being threaded, the blocks a round
    // already changed, and the labels it made.
    tDec: Vec<long>, tDirty: Vec<bool>, tConst: Vec<bool>, threadSeq: long, tConstReady: bool,

    // Scratch for a constant read out of an operand, and an interval read out of the facts.
    cv: long, lo: long, hi: long, sbOff: long,
    // Copies seen in the block being walked (`noteCopy`).
    eqTo: Vec<long>, eqStamp: Vec<long>, eqPos: Vec<long>, walkStamp: long,

    nFolded: long, nAddr: long, nLoads: long, nBranches: long, nChecks: long, nUnreach: long,
    nStrength: long, nReassoc: long, nSkipped: long, nMovs: long, nDead: long, nThreads: long, nDeadStores: long, nShared: long,
    nLentCalls: long, nLentLocals: long, nHoisted: long, nForwarded: long,
    // `forwardResults`: reads per temp, and the results built in place (at the call, in the callee).
    rsUse: Vec<long>, nResults: long, nInPlace: long,
    // `buildWhereCopied`: per frame slot, its first and last access and whether it is read or
    // written by name; per label, where it is and the first and last jump to it.
    wcFirst: HashMap<long, long>, wcLast: HashMap<long, long>, wcNamed: HashMap<long, bool>,
    wcLabel: HashMap<long, long>, wcJumpLo: HashMap<long, long>, wcJumpHi: HashMap<long, long>, nBuilt: long,
    // Loop-invariant code motion (`hoist`): immediate dominators by block and each block's place
    // in reverse postorder; the natural loops (header, blocks as runs of `lpList`, outermost first
    // in `lpOrder`); per temp the loop that defines it; per instruction whether it moved, and the
    // moves in order with their loops; each loop's new entry label (as a number), or -1.
    idom: Vec<long>, rpoNum: Vec<long>,
    lpHead: Vec<long>, lpFirst: Vec<long>, lpCount: Vec<long>, lpList: Vec<long>, lpMark: Vec<long>, lpOrder: Vec<long>,
    lpDef: Vec<long>, hMoved: Vec<bool>, hOrder: Vec<long>, hLoop: Vec<long>, lpLabel: Vec<long>, blockMark: Vec<long>,
    hAt: Vec<long>, hBuf: Vec<Instr>, phSeq: long, hUse: Vec<long>,
    slotRead: HashMap<long, bool>,     // `dropDeadSlots`: the frame slots something reads
    // `forwardCopies`: the block copies in force in the block being walked, each a destination
    // slot, offset and size, and the source's address temp and slot.
    fwDst: Vec<long>, fwOff: Vec<long>, fwSize: Vec<long>, fwSrc: Vec<Temp>, fwSrcRoot: Vec<long>,
    // Common subexpressions (`exprFacts`): per instruction its expression group or -1; per group
    // the expression and its facts as a list (`eHead`, `eNext`); the counting by shape.
    instExpr: Vec<long>, shapeOf: Vec<long>, shapeCount: HashMap<long, long>, eKey: HashMap<long, long>,
    eOp: Vec<IROp>, eA: Vec<Temp>, eB: Vec<Temp>, eImm: Vec<long>, eIsImm: Vec<bool>,
    eKind: Vec<Lit>, eFrom: Vec<Lit>, eTo: Vec<Lit>, eHead: Vec<long>, eNext: Vec<long>, nCse: long,
    // Per temp, a bit k for each signed division of it by 2^k (`lowBitsZero`).
    lowDiv: Vec<long>,
    // Relations made at joins (`deriveJoin`): the candidate facts, and per block the ones whose
    // temp the block defines, as runs of `jcList`.
    jcFirst: Vec<long>, jcCount: Vec<long>, jcList: Vec<long>, jcVals: Vec<Temp>, jcWs: Vec<Temp>,
    // Each temp's first fact against a constant and the next one's, by fact (`joinCandidates`).
    jcImmHead: Vec<long>, jcImmNext: Vec<long>,
    // The counters as this function began, so the cleanup knows what it has to do.
    mark0: long, mark1: long, mark2: long, mark3: long, markF: long, markE: long
}

pub var gFlowOff: bool = false;
pub var gThreadOff: bool = false;     // `--no-thread`: the dataflow without jump threading
pub var gCseOff: bool = false;        // `--no-cse`: the dataflow without common subexpressions
pub var gHoistOff: bool = false;      // `--no-hoist`: no loop-invariant code motion
pub var gWideAddrOff: bool = false;   // `--no-wide-addr`: addresses folded within a block only (`foldAddressesWide`)
pub var gHoistDupOff: bool = false;   // `--no-hoist-dup`: each hoisted load kept, the same one twice or not (`sameHoisted`)
pub var gXorBoundsOff: bool = false;  // `--no-xor-bounds`: no upper bound through `^` or `|` (`boundWalk`)
pub var gWideConstOff: bool = false;  // `--no-wide-const`: a constant past 32 bits is not hoisted (`canHoist`)
// `0 - x` and `~x + 1` as a product by -1, which the emitter writes as `neg` (`--no-neg`).
pub var gNegOff: bool = false;
// `--no-promote-lent`: a local whose address is lent to calls stays in its slot (`promoteLent`).
pub var gPromoteLentOff: bool = false;
// `(x + c) - d` as `x + (c - d)`, and `a - (a - b)` as `b` (`--no-reassociate`).
pub var gReassocOff: bool = false;
// `--no-literal-bytes`: a read of a string literal's bytes stays a read.
pub var gLitBytesOff: bool = false;
pub var gRestrictOff: bool = false;   // `--no-restrict`: no borrowed parameter's bytes trusted to be its own
pub var gRodataOff: bool = false;     // `--no-rodata`: no immutable global's image trusted
pub var gResultsOff: bool = false;    // `--no-results`: aggregate results copied through scratch
pub var gBuildOff: bool = false;      // `--no-build`: a value built in one frame slot and copied whole to another
pub var gResultEachOff: bool = false; // `--no-result-each`: no result built in the caller's memory at each of several returns (`buildInPlaceEach`)

methods Flow for Default {
    new -> Flow {
        return Flow { op: Opt.new(), first: 0, n: 0, base: 0, nt: 0,
                      defs: vec![], defAt: vec![], kStamp: vec![], kVal: vec![], dStamp: vec![], dPos: vec![],
                      nonneg: vec![], acRoot: vec![], acKind: vec![], acOff: vec![], exposed: map![], lent: map![], callFx: vec![], globalAt: map![], roGlobals: vec![], roAny: false, roHere: false, riImage: -1, riOff: 0, roSeen: vec![], hCall: -1,
                      bStart: vec![], bEnd: vec![], bTaken: vec![], bFall: vec![], bCond: vec![], bNeg: vec![],
                      blockOf: vec![], predFirst: vec![], predCount: vec![], predBlock: vec![], predKind: vec![],
                      order: vec![], reach: vec![], labelAt: map![], stack: vec![], stackNext: vec![],
                      fKind: vec![], fOp: vec![], fA: vec![], fB: vec![], fImm: vec![], fIsImm: vec![], fUns: vec![],
                      fLoc: vec![], factKey: map![],
                      lRootKind: vec![], lRoot: vec![], lOff: vec![], lWidth: vec![], lCls: vec![], locKey: map![],
                      instLoc: vec![], instFact: vec![],
                      tfFirst: vec![], tfCount: vec![], tfList: vec![], callKill: vec![], allMem: vec![], tempMem: vec![],
                      fnBorrows: 0, fnUnsafe: true, bpParam: vec![], bpMask: vec![], bpOther: vec![], bpRead: vec![], bpLeak: 0, ownSets: vec![], callOther: vec![], tempOther: vec![], rdLast: vec![], rdPrev: vec![], callAt: vec![], madeMemo: vec![],
                      rootKey: map![], rRk: vec![], rRoot: vec![], rootHead: vec![], tempRootAt: vec![], locNext: vec![],
                      locFactHead: vec![], factNext: vec![], keep: vec![],
                      words: 0, nf: 0, bits: vec![], cur: vec![], addOk: vec![], condHi: vec![], transDepth: 0,
                      rLo: vec![], rHi: vec![], rOn: false, nLo: vec![], nHi: vec![], rDefs: vec![], rFixed: vec![],
                      oaLo: vec![], oaHi: vec![], obLo: vec![], obHi: vec![], oaUp: vec![],
                      cmFirst: vec![], cmCount: vec![], cmSrc: vec![], cmDst: vec![], cmOn: vec![], bDyn: vec![],
                      copies: vec![], copyAt: vec![], needNonneg: false, tStack: vec![], tWritten: vec![], tDefs: vec![], tSeen: vec![], tDec: vec![], tDirty: vec![], tConst: vec![], threadSeq: 0, tConstReady: false,
                      cv: 0, lo: 0, hi: 0, sbOff: 0, eqTo: vec![], eqStamp: vec![], eqPos: vec![], walkStamp: 0,
                      nFolded: 0, nAddr: 0, nLoads: 0, nBranches: 0, nChecks: 0, nUnreach: 0, nStrength: 0, nReassoc: 0, nSkipped: 0, nMovs: 0, nDead: 0, nThreads: 0, nDeadStores: 0, nShared: 0, nLentCalls: 0, nLentLocals: 0, nHoisted: 0, nForwarded: 0, rsUse: vec![], nResults: 0, nInPlace: 0,
                      wcFirst: map![], wcLast: map![], wcNamed: map![], wcLabel: map![], wcJumpLo: map![], wcJumpHi: map![], nBuilt: 0,
                      idom: vec![], rpoNum: vec![], lpHead: vec![], lpFirst: vec![], lpCount: vec![], lpList: vec![], lpMark: vec![], lpOrder: vec![],
                      lpDef: vec![], hMoved: vec![], hOrder: vec![], hLoop: vec![], lpLabel: vec![], blockMark: vec![], hAt: vec![], hBuf: vec![], phSeq: 0, hUse: vec![],
                      slotRead: map![], fwDst: vec![], fwOff: vec![], fwSize: vec![], fwSrc: vec![], fwSrcRoot: vec![],
                      instExpr: vec![], shapeOf: vec![], shapeCount: map![], eKey: map![], eOp: vec![], eA: vec![], eB: vec![],
                      eImm: vec![], eIsImm: vec![], eKind: vec![], eFrom: vec![], eTo: vec![], eHead: vec![], eNext: vec![], nCse: 0, lowDiv: vec![], jcFirst: vec![], jcCount: vec![], jcList: vec![], jcVals: vec![], jcWs: vec![], jcImmHead: vec![], jcImmNext: vec![],
                      mark0: 0, mark1: 0, mark2: 0, mark3: 0, markF: 0, markE: 0 };
    }
}

methods Flow {
    run &self inout p:IRProgram -> void {
        // Before the summaries, which read what each parameter now is.
        ownMovedArgs(p);
        if (gFlowOff) { return; }
        fxBegin(p);
        self.globalAt.clear();
        for g in 0..p.globals.len() { self.globalAt.put(p.globals.get(g) as long, g); }
        self.roGlobals.clear();
        self.roAny = false;
        for g in 0..p.globals.len() {
            n: Sym = p.globals.get(g);
            if (gRodataOff || n == NO_SYM || !(p.globalImage.get(g) >= 0 || p.globalHasInit.get(g)) || isVarGlobal(n)) { continue; }
            while (self.roGlobals.len() <= (n as long)) { self.roGlobals.push(false); }
            self.roGlobals.set(n as long, true);
            self.roAny = true;
        }
        for f in 0..p.funcs.len() {
            if (!gPromoteLentOff) { self.promoteLent(p, f); }
            self.runOne(p, p.funcs.get(f));
        }
        if (gTraceOpt) { eprintln("flow: {} locals lent to calls kept in registers between them", self.nLentLocals); }
        if (gTraceOpt) {
            eprintln("flow: {} folded, {} strength-reduced, {} addresses, {} loads, {} branches, {} checks, {} edges threaded, {} unreachable, {} dead stores, {} common subexpressions, {} copies shared, {} hoisted, {} block copies forwarded, {} results into their place, {} built in the caller's, {} built where they are copied, {} functions skipped; {} functions summarized and {} answered \"everything\", {} calls lent a slot, {} parameters taken in place",
                     self.nFolded, self.nStrength, self.nAddr, self.nLoads, self.nBranches, self.nChecks, self.nThreads, self.nUnreach, self.nDeadStores, self.nCse, self.nShared, self.nHoisted, self.nForwarded, self.nResults, self.nInPlace, self.nBuilt, self.nSkipped, gFxCount, gFxTop, self.nLentCalls, gMovedParams);
        }
    }

    // A scalar local whose address is taken only to be handed to direct calls whose callees keep
    // no pointer to it lives in its promoted temp like any other local, and its slot holds it only
    // across those calls: the temp is stored there before each, and read back after each whose
    // callee may write through the pointer. During such a call the slot is the variable, and no
    // pointer to it outlives the call, so nothing reads or writes the slot at any other time. That
    // a parameter does not escape is the callee's summary (`fxEscapes`: stored nowhere, handed
    // back to no one, given to nothing that keeps it), worked out from the code the callee runs,
    // so an `unsafe` callee is held to what it does rather than to what it may do. A decoder's
    // `readVarLen(&ip, ...)` kept `ip` in the frame through the whole loop around it.
    //
    // Not where a `recover` is (its handler reads variables in their slots), nor for a parameter
    // (its seed is its definition), a name an `asm` block or an array access spells, or one read
    // or written at more than one type. The function's code is copied to the end of the
    // program's with the copies added, as `Opt.unrollAll` does, before the function's own passes.
    promoteLent &self inout p:IRProgram f:long -> void {
        fn: IRFunc = p.funcs.get(f);
        if (fn.instrCount == 0 || hasRecover(p, fn)) { return; }
        // Cheapest first: a scalar local still read or written by name. After `Opt.promoteLocals`
        // that is one it could not promote (its address taken, or an `asm` spelling it); most
        // functions have none.
        any: bool = false;
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            o: IROp = p.code[ix].op;
            if ((o == IROp.Load || o == IROp.Store) && p.code[ix].name != NO_SYM && !p.code[ix].isGlobal && !p.code[ix].paramSeed
                && (isInteger(p.code[ix].kind) || p.code[ix].kind == Lit.Ptr)) { any = true; break; }
        }
        if (!any) { return; }
        // name -> 1 while a candidate, 0 once refused (`lentRefuse`), and the index of a load or
        // store of it, for the type it is read and written at. Most addresses taken are an
        // aggregate's, never read or written by name, so this list usually ends empty here.
        cand: HashMap<long, long>;
        kindAt: HashMap<long, long>;
        seen: Vec<long>;
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            if (p.code[ix].op != IROp.AddrOf || p.code[ix].name == NO_SYM || p.code[ix].isGlobal || p.code[ix].dst == NO_TEMP) { continue; }
            nm: long = p.code[ix].name as long;
            if (!cand.has(nm)) { cand.put(nm, 1); seen.push(nm); }
        }
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            o: IROp = p.code[ix].op;
            if (o == IROp.Asm) {
                for k in 0..p.code[ix].pieceCount {
                    nm: Sym = p.asmNames.get(p.code[ix].firstPiece + k);
                    if (nm != NO_SYM && cand.has(nm as long)) { self.lentRefuse(&cand, nm as long); }
                }
            }
            if ((o == IROp.ArrLoad || o == IROp.ArrStore) && p.code[ix].name != NO_SYM && cand.has(p.code[ix].name as long)) {
                self.lentRefuse(&cand, p.code[ix].name as long);
            }
            if ((o == IROp.Load || o == IROp.Store) && p.code[ix].name != NO_SYM && cand.has(p.code[ix].name as long)) {
                nm: long = p.code[ix].name as long;
                k: Lit = p.code[ix].kind;
                if (p.code[ix].isGlobal || p.code[ix].paramSeed || !(isInteger(k) || k == Lit.Ptr)) { self.lentRefuse(&cand, nm); }
                else if (!kindAt.has(nm)) { kindAt.put(nm, i); }
                else if (p.code[fn.firstInstr + lentGet(kindAt, nm, 0)].kind != k) { self.lentRefuse(&cand, nm); }
            }
        }
        left: bool = false;
        for q in 0..seen.len() {
            if (lentGet(cand, seen.get(q), 0) == 1 && kindAt.has(seen.get(q))) { left = true; }
        }
        if (!left) { return; }
        // Per temp of the function, the name whose address it holds, or -1. One temp holding two
        // names' addresses, an address temp written by anything but its `AddrOf`, or read by
        // anything but a direct call whose callee keeps nothing (`fxEscapes`), refuses its name.
        nt: long = fn.tempCount - fn.firstTemp;
        addr: Vec<long>;
        for t in 0..nt { addr.push(-1); }
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            if (p.code[ix].op != IROp.AddrOf || p.code[ix].name == NO_SYM || p.code[ix].isGlobal || p.code[ix].dst == NO_TEMP) { continue; }
            nm: long = p.code[ix].name as long;
            r: long = p.code[ix].dst - fn.firstTemp;
            if (r < 0 || r >= nt) { self.lentRefuse(&cand, nm); continue; }
            if (addr.get(r) >= 0 && addr.get(r) != nm) { self.lentRefuse(&cand, addr.get(r)); self.lentRefuse(&cand, nm); }
            addr.set(r, nm);
        }
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            o: IROp = p.code[ix].op;
            if (o != IROp.AddrOf) { self.lentRead(&cand, addr, fn.firstTemp, p.code[ix].dst); }
            self.lentRead(&cand, addr, fn.firstTemp, p.code[ix].a);
            if (!p.code[ix].bIsImm) { self.lentRead(&cand, addr, fn.firstTemp, p.code[ix].b); }
            self.lentRead(&cand, addr, fn.firstTemp, p.code[ix].x);
            for k in 0..p.code[ix].pieceCount { self.lentRead(&cand, addr, fn.firstTemp, p.asmVals.get(p.code[ix].firstPiece + k)); }
            na: long = p.code[ix].argCount;
            if (na == 0) { continue; }
            s: long = -2;
            for k in 0..na {
                nm: long = lentAddr(addr, fn.firstTemp, p.args.get(p.code[ix].firstArg + k));
                if (nm < 0) { continue; }
                if (s == -2) { s = -1; if (o == IROp.Call) { s = fxOfCallee(p, p.code[ix].name); } }
                if (o != IROp.Call || s < 0 || k >= fxParams(s) || fxEscapes(s, k)) { self.lentRefuse(&cand, nm); }
            }
        }
        // What is left, with its temp and a type to copy it at.
        names: Vec<long>;
        temps: HashMap<long, long>;
        if (self.op.slotTemp.cap() > 512) { self.op.slotTemp = map![]; } else { self.op.slotTemp.clear(); }
        for q in 0..seen.len() {
            nm: long = seen.get(q);
            if (lentGet(cand, nm, 0) != 1 || !kindAt.has(nm)) { continue; }
            t: Temp = self.op.tempFor(p, fn, nm as Sym);
            if (t == NO_TEMP) { continue; }
            temps.put(nm, t as long);
            names.push(nm);
        }
        if (names.len() == 0) { return; }
        // The copy, the loads and stores of each name its temp's, each call that lends one between
        // a store of the temp to the slot and (where the callee may write there) a load back.
        start: long = p.code.len();
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            nm: long = in.name as long;
            if ((in.op == IROp.Load || in.op == IROp.Store) && in.name != NO_SYM && !in.isGlobal && temps.has(nm)) {
                t: Temp = lentGet(temps, nm, 0) as Temp;
                if (in.op == IROp.Load) {
                    mv: Instr = instr(IROp.Mov);
                    mv.dst = in.dst; mv.a = t; mv.kind = in.kind;
                    mv.structName = in.structName;
                    p.code.push(mv);
                } else if (narrowsInto(p.kindOf(in.a), in.kind)) {
                    cv: Instr = instr(IROp.Convert);
                    cv.dst = t; cv.a = in.a; cv.kind = in.kind;
                    cv.fromKind = p.kindOf(in.a); cv.toKind = in.kind;
                    p.code.push(cv);
                } else {
                    mv: Instr = instr(IROp.Mov);
                    mv.dst = t; mv.a = in.a; mv.kind = in.kind;
                    mv.structName = in.structName;
                    p.code.push(mv);
                }
                continue;
            }
            if (in.op != IROp.Call || in.argCount == 0) { p.code.push(in); continue; }
            s: long = fxOfCallee(p, in.name);
            for k in 0..in.argCount {
                a: Temp = p.args.get(in.firstArg + k);
                nm2: long = lentAddr(addr, fn.firstTemp, a);
                if (nm2 < 0 || !temps.has(nm2)) { continue; }
                // Once per address, however many arguments carry it.
                again: bool = false;
                for q in 0..k { if (p.args.get(in.firstArg + q) == a) { again = true; } }
                if (again) { continue; }
                st: Instr = instr(IROp.PtrStore);
                st.a = a;
                st.b = lentGet(temps, nm2, 0) as Temp;
                st.kind = p.code[fn.firstInstr + lentGet(kindAt, nm2, 0)].kind;
                p.code.push(st);
            }
            p.code.push(in);
            for k in 0..in.argCount {
                a: Temp = p.args.get(in.firstArg + k);
                nm2: long = lentAddr(addr, fn.firstTemp, a);
                if (nm2 < 0 || !temps.has(nm2)) { continue; }
                writes: bool = false;
                for q in 0..in.argCount {
                    if (p.args.get(in.firstArg + q) == a && fxWrites(s, q)) { writes = true; }
                }
                again: bool = false;
                for q in 0..k { if (p.args.get(in.firstArg + q) == a) { again = true; } }
                if (again || !writes) { continue; }
                ld: Instr = instr(IROp.PtrLoad);
                ld.dst = lentGet(temps, nm2, 0) as Temp;
                ld.a = a;
                ld.kind = p.code[fn.firstInstr + lentGet(kindAt, nm2, 0)].kind;
                p.code.push(ld);
            }
        }
        fn.firstInstr = start;
        fn.instrCount = p.code.len() - start;
        p.funcs.set(f, fn);
        self.nLentLocals = self.nLentLocals + names.len();
        // The copies the loads and stores became, propagated as `Opt.promoteLocals` leaves them to be.
        self.op.base = fn.firstTemp;
        self.op.propagateCopies(p, fn);
    }

    // `t`, read or written other than by a direct call's argument list or its `AddrOf`: when it
    // holds a lent candidate's address, that name is refused (`promoteLent`).
    lentRead &self inout cand:HashMap<long, long> addr:Vec<long> base:Temp t:Temp -> void {
        nm: long = lentAddr(addr, base, t);
        if (nm >= 0) { self.lentRefuse(cand, nm); }
    }
    lentRefuse &self inout cand:HashMap<long, long> nm:long -> void {
        if (nm >= 0) { cand.put(nm, 0); }
    }

    runOne &self inout p:IRProgram fn:IRFunc -> void {
        if (fn.instrCount == 0) { return; }
        self.first = fn.firstInstr;
        self.n = fn.instrCount;
        self.base = fn.firstTemp;
        self.nt = fn.tempCount - fn.firstTemp;
        if (self.nt < 0) { self.nt = 0; }
        if (!self.wellFormed(p)) { self.nSkipped = self.nSkipped + 1; return; }
        // A function holding a `recover` is left as the lowerer wrote it. Its handler can be
        // entered after any call in the body (`FaultEdge`), and the rewrites here (threading
        // edges, moving code out of loops, forwarding a store to a later load) were built for a
        // graph where every edge is a branch someone may point elsewhere. Such functions are few
        // and small: what they guard is in the functions they call, which are optimized as usual.
        if (hasRecover(p, fn)) { self.nSkipped = self.nSkipped + 1; return; }
        self.fnBorrows = fn.borrows;
        self.fnUnsafe = fn.isUnsafe;
        // What is read through a pointer is in a read-only image only where the function takes the
        // address of a read-only global; most never do, and are not asked.
        self.roHere = false;
        if (self.roAny) {
            for i in 0..self.n {
                ix: long = self.first + i;
                if (p.code[ix].op == IROp.AddrOf && p.code[ix].isGlobal && self.isRo(p.code[ix].name as long)) { self.roHere = true; break; }
            }
        }
        self.mark0 = self.nMovs;
        self.markF = self.nBranches + self.nThreads;
        self.markE = self.nDead + self.nLoads + self.nBranches;
        self.mark1 = self.nFolded + self.nStrength;
        self.mark2 = self.nBranches + self.nChecks + self.nThreads;
        self.mark3 = self.nLoads + self.nFolded + self.nStrength + self.nAddr + self.nBranches + self.nChecks + self.nUnreach + self.nThreads + self.nDeadStores + self.nCse + self.nShared + self.nResults + self.nInPlace + self.nBuilt;
        self.countDefs(p);
        self.foldConstants(p);
        self.foldAddresses(p);
        self.shareCopies(p);
        self.maskZeroTests(p);
        self.buildBlocks(p);
        self.removeUnreachable(p);
        self.thread(p);
        solved: bool = false;
        // The dataflow and its rewrites. They run once more when they leave a join block that its
        // predecessors' stores decide (`threadPastSlots`), which happens once the read that hid
        // the stored value has been forwarded away.
        passes: long = 0;
        while (passes < 2) {
            if (passes > 0) { self.countDefs(p); }
            if (!self.collectFacts(p)) {
                if (passes == 0) { self.nSkipped = self.nSkipped + 1; }
                break;
            }
            passes = passes + 1;
            solved = true;
            // The solve asks `decide` for the relations it makes at joins, and nothing about
            // ranges is known yet: what the last function left there is another function's.
            self.nonneg.clear();
            self.rOn = false;
            self.solve(p);
            // Only a comparison with a constant, a bounds check or a division asks whether a
            // value can be negative.
            self.nonneg.clear();
            self.rOn = false;
            if (self.needNonneg) {
                self.rangeSetup(p);
                self.boundWalk(p);
                self.computeRanges(p);
                self.computeNonneg(p);
            }
            before: long = self.nLoads + self.nBranches + self.nChecks + self.nStrength;
            beforeR: long = self.nReassoc;
            self.rewrite(p);
            // A load that became a copy of a constant makes what reads it foldable in turn, and a
            // decided branch leaves code no path reaches.
            if (self.nLoads + self.nBranches + self.nChecks + self.nStrength > before) {
                self.foldConstants(p);
                self.decideSameConsts(p);
                self.buildBlocks(p);
                self.removeUnreachable(p);
            }
            if (passes == 2) { break; }
            if (self.threadPastSlots(p)) {
                self.nThreads = self.nThreads + 1;
                self.buildBlocks(p);
                self.removeUnreachable(p);
            } else if (self.nReassoc == beforeR) {
                break;
            }
            // Or an address those folds made the same as one already read (`a + n - 4` with `n`
            // 4 is `a`): the dataflow again, which finds the second read the first.
        }
        self.forwardCopies(p);
        self.dropDeadSlots(p);
        if (solved) { self.hoist(p); }
        // Before `forwardResults`, whose half in the callee hands a slot the `$sret` memory: a
        // value built where it is copied is then built in the caller's.
        if (solved && !gBuildOff) { self.buildWhereCopied(p, fn.name); }
        if (solved && !gResultsOff) { self.forwardResults(p, fn.name); }
        if (solved && !gWideAddrOff) { self.foldAddressesWide(p); }
        // What the rewrites leave: copies to propagate, constants to carry as immediates, jumps to
        // nowhere, dead definitions. Each only where this function had a rewrite that leaves one.
        self.op.base = fn.firstTemp;
        if (self.nMovs > self.mark0) { self.op.propagateCopies(p, fn); }
        if (self.nFolded + self.nStrength > self.mark1) { self.op.selectImmediates(p, fn); }
        if (self.nBranches + self.nChecks + self.nThreads > self.mark2) { self.op.simplifyJumps(p, fn); }
        if (self.nLoads + self.nFolded + self.nStrength + self.nAddr + self.nBranches + self.nChecks + self.nUnreach + self.nThreads + self.nDeadStores + self.nCse + self.nShared + self.nResults + self.nInPlace + self.nBuilt > self.mark3) {
            self.sweep(p);
        }
        // A decided branch can leave a truth value computed right before the branch that tests
        // it, with a label nothing jumps to any more and a copy between them (a `bool` an inlined
        // body returned through its end label). Without the label the copy propagates, and the
        // compare and the branch fuse again.
        if (self.nBranches + self.nThreads > self.markF) {
            self.op.dropUnusedLabels(p, fn);
            self.op.propagateCopies(p, fn);
            self.sweep(p);
            self.op.selectImmediates(p, fn);
            self.op.fuseBranches(p, fn);
        } else if (self.nMovs > self.mark0 && self.op.compareThenBranch(p, fn)) {
            // A load found again or a value computed again was a copy, which could stand between
            // a comparison and the branch on it (a closure returning `x > limit` to a loop's
            // `if`); propagated and swept above, the two are next to each other again.
            self.op.countUses(p, fn);
            self.op.fuseBranches(p, fn);
        }
        // A block threading left holding a constant it tested, dead now and swept, is one more
        // block of nothing but a branch.
        // What the rewrites took out of a loop can leave it doing nothing anyone sees, or a branch
        // to the next instruction over an arm left empty (`Opt.dropEmptyLoops`).
        if (!gEmptyLoopsOff && self.nDead + self.nLoads + self.nBranches > self.markE) {
            self.op.simplifyJumps(p, fn);
            self.op.countUses(p, fn);
            if (self.op.dropEmptyLoops(p, fn)) {
                self.op.simplifyJumps(p, fn);
                self.op.dropUnusedLabels(p, fn);
                self.sweep(p);
            }
        }
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

    // Whether every operand an instruction reads is there. A missing one is a construct the
    // lowerer does not support and lowered to nothing. The emitter then reads whatever `rax`
    // holds, and a function whose meaning is a register's leftovers is left exactly as it is.
    wellFormed &self inout p:IRProgram -> bool {
        for i in 0..self.n {
            o0: IROp = p.code[self.first + i].op;
            if (o0 == IROp.Nop || o0 == IROp.Label) { continue; }
            in: Instr = p.code.get(self.first + i);
            o: IROp = in.op;
            bMissing: bool = !in.bIsImm && in.b == NO_TEMP;
            if (o == IROp.PtrStore || o == IROp.Jcc || isCompare(o) || isArith(o) || o == IROp.ArrStore
                || o == IROp.Bounds || o == IROp.AggCopy || o == IROp.MemCopy) {
                if (in.a == NO_TEMP || bMissing) { return false; }
            }
            if (o == IROp.MemCopy && in.argCount != 1) { return false; }
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
            d: Temp = p.code[self.first + i].dst;
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

    // `t` is written by exactly one instruction, a string literal's pair address (`StrLitVal`):
    // the literal's index is left in `cv`.
    // Through copies and the view conversions (`lit as [u8]`), each the temp's one definition.
    strLitAt &self inout p:IRProgram t0:Temp -> bool {
        t: Temp = t0;
        hops: long = 0;
        while (hops < 8) {
            r: long = self.rel(t);
            if (r < 0 || self.defs.get(r) != 1) { return false; }
            d: Instr = p.code.get(self.first + self.defAt.get(r));
            if (d.op == IROp.StrLitVal) { self.cv = d.imm; return true; }
            if (d.op != IROp.Mov && !addressConvert(d)) { return false; }
            t = d.a;
            hops = hops + 1;
        }
        return false;
    }

    // `t` is written by exactly one instruction, an address in a string literal's bytes: the
    // literal's index is left in `cv` and the offset into it in `sbOff`. Through copies, a pointer
    // taken as a word and back, and constants added or taken away, each the temp's one definition.
    strBytesAt &self inout p:IRProgram t0:Temp -> bool {
        t: Temp = t0;
        off: long = 0;
        hops: long = 0;
        while (hops < 8) {
            r: long = self.rel(t);
            if (r < 0 || self.defs.get(r) != 1) { return false; }
            d: Instr = p.code.get(self.first + self.defAt.get(r));
            if (d.op == IROp.StrAddr) { self.cv = d.imm; self.sbOff = off; return true; }
            if (d.op == IROp.Add && self.bConst(p, d, 0)) { off = off + self.cv; }
            else if (d.op == IROp.Sub && self.bConst(p, d, 0)) { off = off - self.cv; }
            else if (d.op == IROp.Convert && !addressConvert(d)
                     && (kindWidth(d.fromKind) != 8 || kindWidth(d.toKind) != 8 || isFloatKind(d.fromKind) || isFloatKind(d.toKind))) { return false; }
            else if (d.op != IROp.Mov && d.op != IROp.Convert) { return false; }
            t = d.a;
            hops = hops + 1;
        }
        return false;
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
            o0: IROp = p.code[at].op;
            if (o0 == IROp.Label) { stamp = stamp + 1; continue; }
            if (o0 == IROp.Nop) { continue; }
            in: Instr = p.code.get(at);
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

    // A branch on a temp every definition of which is the same constant: a truth value set on
    // two paths (`&&` written out, both of its sides folded to 1) is that constant where it is
    // tested, though no single definition reaches it. Asked after the rewrites, which are what
    // turn such definitions into constants.
    decideSameConsts &self inout p:IRProgram -> void {
        fillLong(&self.kStamp, self.nt, 0);      // 0 no definition, 1 one constant, 2 anything else
        fillLong(&self.kVal, self.nt, 0);
        for i in 0..self.n {
            ix: long = self.first + i;
            r: long = self.rel(p.code[ix].dst);
            if (r < 0 || p.code[ix].op == IROp.Nop) { continue; }
            st: long = self.kStamp.get(r);
            if (p.code[ix].op != IROp.Const) { self.kStamp.set(r, 2); }
            else if (st == 0) { self.kStamp.set(r, 1); self.kVal.set(r, p.code[ix].imm); }
            else if (st == 1 && self.kVal.get(r) != p.code[ix].imm) { self.kStamp.set(r, 2); }
        }
        for i in 0..self.n {
            ix: long = self.first + i;
            o: IROp = p.code[ix].op;
            if (o != IROp.Jz && o != IROp.Jcc) { continue; }
            in: Instr = p.code.get(ix);
            ra: long = self.rel(in.a);
            if (ra < 0 || self.kStamp.get(ra) != 1) { continue; }
            x: long = self.kVal.get(ra);
            if (o == IROp.Jz) {
                self.decideBranch(&in, x == 0);
            } else {
                if (isFloatKind(in.kind)) { continue; }
                y: long = in.bImm;
                if (!in.bIsImm) {
                    rb: long = self.rel(in.b);
                    if (rb < 0 || self.kStamp.get(rb) != 1) { continue; }
                    y = self.kVal.get(rb);
                }
                self.decideBranch(&in, compareHolds(in.cmpOp, canon(in.kind, x), canon(in.kind, y), kindUnsigned(in.kind)));
            }
            p.code.set(ix, in);
        }
    }

    // Whether temp `t` holds an exact address in a read-only image: a `roGlobals` global's, or a
    // block one of them owns, reached by loading the pointer its image holds. Found through single
    // definitions (an address, a copy, a constant added, a pointer loaded); the image is left in
    // `riImage` and the offset in `riOff`.
    roImageOf &self inout p:IRProgram t:Temp depth:long -> bool {
        if (depth > 6) { return false; }
        r: long = self.rel(t);
        if (r < 0 || self.defs.get(r) != 1 || self.defAt.get(r) < 0) { return false; }
        ix: long = self.first + self.defAt.get(r);
        o: IROp = p.code[ix].op;
        if (o == IROp.AddrOf) {
            n: Sym = p.code[ix].name;
            if (!p.code[ix].isGlobal || n == NO_SYM || !self.isRo(n as long)) { return false; }
            g: long = self.globalAt.getOr(n as long, -1);
            if (g < 0 || p.globalImage.get(g) < 0) { return false; }
            self.riImage = p.globalImage.get(g);
            self.riOff = 0;
            return true;
        }
        if (o == IROp.Mov) { return self.roImageOf(p, p.code[ix].a, depth + 1); }
        in: Instr = p.code.get(ix);
        if (addressConvert(in)) { return self.roImageOf(p, in.a, depth + 1); }
        if (o == IROp.Add) {
            if (!self.bConst(p, in, 0)) { return false; }
            k: long = self.cv;
            if (!self.roImageOf(p, in.a, depth + 1)) { return false; }
            self.riOff = self.riOff + k;
            return true;
        }
        if (o == IROp.PtrLoad && in.x == NO_TEMP && kindWidth(in.kind) == 8) {
            if (!self.roImageOf(p, in.a, depth + 1)) { return false; }
            img: long = self.riImage;
            at: long = self.riOff + in.imm;
            f: long = p.imageRelocFirst.get(img);
            for q in f..f + p.imageRelocCount.get(img) {
                if (p.relocOffset.get(q) != at) { continue; }
                if (p.relocKind.get(q) != RelocKind.Block) { return false; }
                self.riImage = p.relocTarget.get(q);
                self.riOff = p.relocDelta.get(q);
                return true;
            }
        }
        return false;
    }
    isRo &self n:long -> bool { return n >= 0 && n < self.roGlobals.len() && self.roGlobals.get(n); }
    // `roRoot`, asked once per temp in a function (`roSeen`: 1 not yet, 2 no, 3 yes).
    roRootMemo &self inout p:IRProgram t:Temp -> bool {
        r: long = self.rel(t);
        if (r < 0) { return false; }
        if (self.roSeen.len() != self.nt) { fillLong(&self.roSeen, self.nt, 1); }
        m: long = self.roSeen.get(r);
        if (m != 1) { return m == 3; }
        yes: bool = self.roRoot(p, t, 0);
        if (yes) { self.roSeen.set(r, 3); } else { self.roSeen.set(r, 2); }
        return yes;
    }
    // Whether `t` is an address somewhere in a read-only image: an exact one, or one an index was
    // added to (an address plus an integer stays in its object).
    roRoot &self inout p:IRProgram t:Temp depth:long -> bool {
        if (self.roImageOf(p, t, 0)) { return true; }
        if (depth > 6) { return false; }
        r: long = self.rel(t);
        if (r < 0 || self.defs.get(r) != 1 || self.defAt.get(r) < 0) { return false; }
        ix: long = self.first + self.defAt.get(r);
        o: IROp = p.code[ix].op;
        if (o == IROp.Mov || o == IROp.Add || o == IROp.Sub) { return self.roRoot(p, p.code[ix].a, depth + 1); }
        return false;
    }

    // Rewrites `in` in place when it folds; says whether it did.
    foldOne &self inout p:IRProgram inout in:Instr stamp:long -> bool {
        o: IROp = in.op;
        if (o == IROp.Const) { return false; }
        // A read of a constant offset in a read-only image (a global the compiler computed, or a
        // block its value owns): the bytes the image holds there, unless a pointer is laid there.
        if (o == IROp.PtrLoad && in.x == NO_TEMP && foldableKind(in.kind) && !isFloatKind(in.kind) && self.roHere && self.roImageOf(p, in.a, 0)) {
            img: long = self.riImage;
            off: long = self.riOff + in.imm;
            w: long = kindWidth(in.kind);
            if (off >= 0 && off + w <= p.imageCount.get(img) && !relocWithin(p, img, off, w)) {
                v: long = 0;
                k: long = w;
                b0: long = p.imageFirst.get(img) + off;
                while (k > 0) { k = k - 1; v = (v << 8) | (p.imageBytes.get(b0 + k) as long); }
                makeConst(in, canon(in.kind, v));
                return true;
            }
        }
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
        // A word of a string literal's {ptr, len} pair. The assembler writes the pair and nothing
        // in the program writes it again: a `str` value is copied wherever it is stored, and a
        // `str` parameter copies its pair before it changes it (`lower.k` `ownCopy`), so no code
        // holds the literal's own address where it could write. The `len` is the literal's
        // length, and the `ptr` the address of its bytes.
        if (o == IROp.PtrLoad && in.x == NO_TEMP && kindWidth(in.kind) == 8 && self.strLitAt(p, in.a)) {
            if (in.imm == 8 && foldableKind(p.kindOf(in.dst))) {
                makeConst(in, literalLength(nameOf(p.strings.get(self.cv))));
                return true;
            }
            if (in.imm == 0 && p.kindOf(in.dst) == Lit.Ptr) {
                d: Temp = in.dst;
                in = instr(IROp.StrAddr);
                in.dst = d;
                in.imm = self.cv;
                in.kind = Lit.Ptr;
                return true;
            }
        }
        // A read of a string literal's bytes at a known offset: what the assembler writes there.
        // A `str` is immutable, its literal's bytes read-only data (docs/language.md), so nothing
        // writes them again.
        if (o == IROp.PtrLoad && in.x == NO_TEMP && !gLitBytesOff && foldableKind(in.kind) && !isFloatKind(in.kind)
            && in.kind != Lit.Ptr && in.kind != Lit.Ref && self.strBytesAt(p, in.a)) {
            text: str = nameOf(p.strings.get(self.cv));
            off: long = self.sbOff + in.imm;
            k: long = kindWidth(in.kind);
            v: long = 0;
            while (off >= 0 && k > 0) {
                k = k - 1;
                b: long = literalByte(text, off + k);
                if (b < 0) { return false; }
                v = (v << 8) | b;
            }
            if (off < 0) { return false; }
            makeConst(in, canon(in.kind, v));
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
        if (o == IROp.Jcc && self.xorTest(p, in)) { return true; }
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
        if (!ka && !kb) { return self.subOfSub(p, in); }
        return self.identity(p, in, ka, x, kb, y);
    }

    // A branch on `(a ^ b) == 0` (or `!=`) is a branch on `a == b`: one compare where the two
    // took an `xor` and a test. `a` and `b` are each written once, or `b` is a constant.
    xorTest &self inout p:IRProgram inout in:Instr -> bool {
        if (gReassocOff || (in.cmpOp != IROp.CmpEq && in.cmpOp != IROp.CmpNe) || isFloatKind(in.kind)) { return false; }
        if (!self.bConst(p, in, 0) || self.cv != 0) { return false; }
        r: long = self.rel(in.a);
        if (r < 0 || self.defs.get(r) != 1) { return false; }
        def: Instr = p.code.get(self.first + self.defAt.get(r));
        hops: long = 0;
        while (def.op == IROp.Mov && def.kind == in.kind && hops < 4) {
            r = self.rel(def.a);
            if (r < 0 || self.defs.get(r) != 1) { return false; }
            def = p.code.get(self.first + self.defAt.get(r));
            hops = hops + 1;
        }
        if (def.op != IROp.BXor || def.kind != in.kind) { return false; }
        ra: long = self.rel(def.a);
        if (ra < 0 || self.defs.get(ra) != 1) { return false; }
        if (!def.bIsImm) {
            rb: long = self.rel(def.b);
            if (rb < 0 || self.defs.get(rb) != 1) { return false; }
        }
        in.a = def.a;
        in.b = def.b;
        in.bIsImm = def.bIsImm;
        in.bImm = def.bImm;
        self.nReassoc = self.nReassoc + 1;
        return true;
    }

    // `a - (a - b)` is `b`: a view's length after its start, `s[s.len - n..]`. `a` and `b` are
    // each written once, so each holds one value at both instructions.
    // And `t | t`, `t & t` (`t`), `t ^ t` (0): the same temp read by one instruction is one value.
    subOfSub &self inout p:IRProgram inout in:Instr -> bool {
        if (in.bIsImm || gReassocOff || isFloatKind(in.kind)) { return false; }
        if (in.a == in.b && in.a != NO_TEMP) {
            if (in.op == IROp.BXor) { makeConst(in, 0); self.nReassoc = self.nReassoc + 1; return true; }
            if ((in.op == IROp.BOr || in.op == IROp.BAnd) && p.kindOf(in.a) == in.kind) {
                makeMov(in, in.a);
                self.nMovs = self.nMovs + 1;
                self.nReassoc = self.nReassoc + 1;
                return true;
            }
        }
        if (in.op != IROp.Sub || kindWidth(in.kind) != 8) { return false; }
        r: long = self.rel(in.b);
        ra: long = self.rel(in.a);
        if (r < 0 || ra < 0 || self.defs.get(r) != 1 || self.defs.get(ra) != 1) { return false; }
        def: Instr = p.code.get(self.first + self.defAt.get(r));
        if (def.op != IROp.Sub || def.kind != in.kind) { return false; }
        if (def.a != in.a) {
            root: Temp = self.copyRoot(p, in.a);
            rr: long = self.rel(root);
            if (root != self.copyRoot(p, def.a) || rr < 0 || self.defs.get(rr) != 1) { return false; }
        }
        self.nReassoc = self.nReassoc + 1;
        if (def.bIsImm) { makeConst(in, def.bImm); return true; }
        rb: long = self.rel(def.b);
        if (rb < 0 || self.defs.get(rb) != 1) { return false; }
        makeMov(in, def.b);
        self.nMovs = self.nMovs + 1;
        return true;
    }

    // What `t` is a copy of, through copies each the temp's one definition: `t` itself if none.
    copyRoot &self inout p:IRProgram t0:Temp -> Temp {
        t: Temp = t0;
        hops: long = 0;
        while (hops < 8) {
            r: long = self.rel(t);
            if (r < 0 || self.defs.get(r) != 1) { return t; }
            ix: long = self.first + self.defAt.get(r);
            if (p.code[ix].op != IROp.Mov) { return t; }
            t = p.code[ix].a;
            hops = hops + 1;
        }
        return t;
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
            // `0 - x` is `x * -1`: one `neg` in place of a zeroed register and a `sub`.
            if (o == IROp.Sub && x == 0 && !in.bIsImm && !gNegOff) {
                in.op = IROp.Mul;
                in.a = in.b;
                in.b = NO_TEMP;
                in.bIsImm = true;
                in.bImm = -1;
                self.nStrength = self.nStrength + 1;
                return true;
            }
            if (o == IROp.BAnd && x == 0) { makeConst(in, 0); return true; }
            return false;
        }
        keep: bool = sameWidth || p.kindOf(in.a) == in.kind;
        // `(x + c) - c`, `(x - c) + c` and the rest: `x`, with `x` written once so it holds the
        // same value at both. What a view's start and length leave behind once a constant length
        // reaches them (`a + n - 4` with `n` 4).
        if ((o == IROp.Add || o == IROp.Sub) && sameWidth && !gReassocOff) {
            r: long = self.rel(in.a);
            if (r >= 0 && self.defs.get(r) == 1) {
                def: Instr = p.code.get(self.first + self.defAt.get(r));
                xr: long = self.rel(def.a);
                if ((def.op == IROp.Add || def.op == IROp.Sub) && def.kind == in.kind && xr >= 0 && self.defs.get(xr) == 1
                    && def.a != in.dst && self.bConst(p, def, 0)) {
                    c: long = self.cv;
                    if (def.op == IROp.Sub) { c = 0 - c; }
                    if (o == IROp.Add) { c = c + y; } else { c = c - y; }
                    // Only where the constants cancel: a step folded into one nearer `x` makes the
                    // value-range walks (`interval`) go through it again from every reader, which
                    // on this compiler cost more than the steps saved.
                    if (c == 0) { makeMov(in, def.a); self.nMovs = self.nMovs + 1; self.nReassoc = self.nReassoc + 1; return true; }
                }
            }
        }
        // `~x + 1` is `x * -1`, with `x` written once so it is the same value at both: one `neg`
        // where the two took a copy, a `not` and an `add`.
        if (o == IROp.Add && y == 1 && !gNegOff) {
            r: long = self.rel(in.a);
            if (r >= 0 && self.defs.get(r) == 1) {
                def: Instr = p.code.get(self.first + self.defAt.get(r));
                zr: long = self.rel(def.a);
                if (def.op == IROp.BNot && def.kind == in.kind && zr >= 0 && self.defs.get(zr) == 1) {
                    in.op = IROp.Mul;
                    in.a = def.a;
                    in.b = NO_TEMP;
                    in.bIsImm = true;
                    in.bImm = -1;
                    self.nStrength = self.nStrength + 1;
                    return true;
                }
            }
        }
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
            o0: IROp = p.code[at].op;
            if (o0 == IROp.Label) { stamp = stamp + 1; continue; }
            if (o0 != IROp.PtrLoad && o0 != IROp.PtrStore) {
                // Only where it was defined, read in place.
                r0: long = self.rel(p.code[at].dst);
                if (r0 >= 0) { self.dStamp.set(r0, stamp); self.dPos.set(r0, i); }
                continue;
            }
            in: Instr = p.code.get(at);
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

    // `[t + o]` where `t = x + k` anywhere, both written once, becomes `[x + k + o]` where the
    // definition of `t` dominates the access: `x` then holds there what it held when `t` was made.
    // What the block-local fold cannot reach: an address common subexpressions shared between
    // blocks, or one the hoist moved out of a loop, which otherwise holds a register the whole loop.
    foldAddressesWide &self inout p:IRProgram -> void {
        self.countDefs(p);
        self.buildBlocks(p);
        if (self.bStart.len() == 0) { return; }
        self.dominators();
        for i in 0..self.n {
            at: long = self.first + i;
            o: IROp = p.code[at].op;
            if (o != IROp.PtrLoad && o != IROp.PtrStore) { continue; }
            if (p.code[at].a == NO_TEMP) { continue; }
            ub: long = self.blockOf.get(i);
            if (ub < 0 || !self.reach.get(ub)) { continue; }
            in: Instr = p.code.get(at);
            changed: bool = false;
            hops: long = 0;
            while (hops < 6) {
                hops = hops + 1;
                r: long = self.rel(in.a);
                if (r < 0 || self.defs.get(r) != 1) { break; }
                d: long = self.defAt.get(r);
                def: Instr = p.code.get(self.first + d);
                db: long = self.blockOf.get(d);
                if (db < 0 || !self.reach.get(db) || !self.dominates(db, ub) || (db == ub && d > i)) { break; }
                // Through a copy, of a temp written once: it holds the same there.
                if (def.op == IROp.Mov && def.a != NO_TEMP && !isAggregate(def.kind) && widthOf(def.kind) == 8) {
                    mr: long = self.rel(def.a);
                    if (mr < 0 || self.defs.get(mr) != 1) { break; }
                    in.a = def.a;
                    changed = true;
                    continue;
                }
                if (def.op != IROp.Add || def.a == NO_TEMP || widthOf(def.kind) != 8) { break; }
                k: long = 0;
                if (def.bIsImm) { k = def.bImm; } else if (self.singleConst(p, def.b)) { k = self.cv; } else { break; }
                xr: long = self.rel(def.a);
                if (xr < 0 || self.defs.get(xr) != 1) { break; }
                sum: long = in.imm + k;
                if (k < IMM_LO || k > IMM_HI || sum < IMM_LO || sum > IMM_HI) { break; }
                in.a = def.a;
                in.imm = sum;
                changed = true;
            }
            if (changed) { p.code.set(at, in); self.nAddr = self.nAddr + 1; }
        }
    }

    // ─── loop-invariant code motion (`hoist`) ───────────────────────────────
    //
    // An instruction in a loop whose value is the same on every trip runs once, before the loop,
    // in a preheader: instructions put just before the header's label, which the entry edges run
    // and the back edges (which jump to the label) skip.
    //
    // What moves is a definition that is the only one of its temp, whose operands no instruction
    // of the loop defines, and which is one of these (`canHoist`):
    //
    //   * a pure operation: arithmetic, a comparison, a conversion, an address, a copy, or a
    //     division by a constant that cannot fault (`hoistableOp`);
    //   * a load whose location nothing in the loop may write, and which is safe to run where it
    //     did not run before. Each instruction of the loop is asked whether it writes the location
    //     just as the dataflow asks it (`killMem`, with calls through their summaries). The load
    //     is safe when it reads a frame slot or a global, reads through a borrow (a `&T` always
    //     points at a live `T`) or through a `str`, slice or trait object (whose value is the
    //     address of a live pair: a parameter's is the caller's, and every other one is a
    //     literal's or a slot's), or sits in the header itself, which runs whenever the preheader
    //     does.
    //
    // Floats stay in the loop, and so does everything in a loop that makes a call; the reasons
    // are measured and given where each is refused.
    //
    // Loops are the natural ones (a back edge to a block that dominates its source), taken
    // outermost first, so an instruction invariant in an outer loop leaves both. When the entry
    // reaches the header only by falling into its label, the preheader is just the code before
    // it. Entry jumps are sent to a new label put in front of the preheader (`.PHn`), which takes
    // the place of a deleted instruction so that the function's run keeps its length. A loop whose
    // body falls into its own header is left alone.
    hoist &self inout p:IRProgram -> void {
        nb: long = self.bStart.len();
        if (nb < 2 || gHoistOff) { return; }
        self.dominators();
        // The loops: per header, its blocks, as runs in one flat list.
        self.lpHead.clear(); self.lpFirst.clear(); self.lpCount.clear(); self.lpList.clear();
        fillLong(&self.lpMark, nb, -1);
        for oi in 0..self.order.len() {
            h: long = self.order.get(oi);
            latch: bool = false;
            pf: long = self.predFirst.get(h);
            for k in 0..self.predCount.get(h) {
                u: long = self.predBlock.get(pf + k);
                if (self.reach.get(u) && self.dominates(h, u)) { latch = true; }
            }
            if (!latch) { continue; }
            // Every block that reaches a latch without passing the header.
            id: long = self.lpHead.len();
            self.lpHead.push(h);
            self.lpFirst.push(self.lpList.len());
            self.lpList.push(h);
            self.lpMark.set(h, id);
            self.stack.clear();
            for k in 0..self.predCount.get(h) {
                u: long = self.predBlock.get(pf + k);
                if (self.reach.get(u) && self.dominates(h, u) && self.lpMark.get(u) != id) {
                    self.lpMark.set(u, id);
                    self.lpList.push(u);
                    self.stack.push(u);
                }
            }
            while (self.stack.len() > 0) {
                b: long = self.stack.pop();
                bf: long = self.predFirst.get(b);
                for k in 0..self.predCount.get(b) {
                    u: long = self.predBlock.get(bf + k);
                    if (self.reach.get(u) && self.lpMark.get(u) != id) {
                        self.lpMark.set(u, id);
                        self.lpList.push(u);
                        self.stack.push(u);
                    }
                }
            }
            self.lpCount.push(self.lpList.len() - self.lpFirst.get(id));
        }
        nl: long = self.lpHead.len();
        if (nl == 0) { return; }
        // Outermost first: a loop holding another is the larger.
        self.lpOrder.clear();
        for k in 0..nl { self.lpOrder.push(k); }
        for a in 1..nl {
            x: long = self.lpOrder.get(a);
            j: long = a;
            while (j > 0 && self.lpCount.get(self.lpOrder.get(j - 1)) < self.lpCount.get(x)) {
                self.lpOrder.set(j, self.lpOrder.get(j - 1));
                j = j - 1;
            }
            self.lpOrder.set(j, x);
        }
        // The deleted instructions a new label may take the place of.
        spare: long = 0;
        for i in 0..self.n { if (p.code[self.first + i].op == IROp.Nop) { spare = spare + 1; } }
        self.countDefs(p);
        fillLong(&self.lpDef, self.nt, -1);
        fillBool(&self.hMoved, self.n, false);
        self.hOrder.clear(); self.hLoop.clear();
        fillLong(&self.lpLabel, nl, -1);
        fillLong(&self.blockMark, nb, -1);
        planned: long = 0;
        for q in 0..nl {
            k: long = self.lpOrder.get(q);
            h: long = self.lpHead.get(k);
            hs: long = self.bStart.get(h);
            if (p.code[self.first + hs].op != IROp.Label) { continue; }
            for z in 0..self.lpCount.get(k) { self.blockMark.set(self.lpList.get(self.lpFirst.get(k) + z), k); }
            // The entry edges: some, none falling in from inside, and a label for any that jumps.
            outside: long = 0;
            jumps: bool = false;
            inFall: bool = false;
            pf: long = self.predFirst.get(h);
            for e in 0..self.predCount.get(h) {
                u: long = self.predBlock.get(pf + e);
                if (!self.reach.get(u)) { continue; }
                inside: bool = self.blockMark.get(u) == k;
                if (inside) { if (self.predKind.get(pf + e) == E_FALL) { inFall = true; } continue; }
                outside = outside + 1;
                if (self.predKind.get(pf + e) == E_TAKEN) { jumps = true; }
            }
            if (outside == 0 || inFall || (jumps && spare == 0)) { continue; }
            // A loop that makes a call (one that returns) is left as it is. What crosses a call
            // lives in one of four callee-saved registers or in the frame, and a hoisted value
            // that ends up in the frame is reloaded at each use, where it had been a load or an
            // `lea` anyway. Measured, the merge sort and the hash kernel got slower, and so did
            // the compiler's own loops.
            calls: bool = false;
            for z in 0..self.lpCount.get(k) {
                b: long = self.lpList.get(self.lpFirst.get(k) + z);
                for i in self.bStart.get(b)..self.stopOf(b) {
                    oc: IROp = p.code[self.first + i].op;
                    if ((oc == IROp.Call && !p.code[self.first + i].noReturn) || oc == IROp.CallIndirect || oc == IROp.Asm) { calls = true; }
                }
            }
            if (calls) { continue; }
            // What the loop defines.
            for z in 0..self.lpCount.get(k) {
                b: long = self.lpList.get(self.lpFirst.get(k) + z);
                for i in self.bStart.get(b)..self.stopOf(b) {
                    if (self.hMoved.get(i)) { continue; }
                    r: long = self.rel(p.code[self.first + i].dst);
                    if (r >= 0) { self.lpDef.set(r, k); }
                }
            }
            before: long = self.hOrder.len();
            going: bool = true;
            rounds: long = 0;
            while (going && rounds < 4) {
                going = false;
                rounds = rounds + 1;
                for oi in 0..self.order.len() {
                    b: long = self.order.get(oi);
                    if (self.blockMark.get(b) != k) { continue; }
                    for i in self.bStart.get(b)..self.stopOf(b) {
                        if (self.hMoved.get(i) || !self.canHoist(p, i, h, k)) { continue; }
                        // The same load again (two copies of one inlined body read one field):
                        // once in the preheader, and this one a copy of it.
                        if (!gHoistDupOff) { self.sameHoisted(p, i, k, before); }
                        self.hMoved.set(i, true);
                        self.hOrder.push(i);
                        self.hLoop.push(k);
                        self.lpDef.set(self.rel(p.code[self.first + i].dst), -1);
                        going = true;
                    }
                }
            }
            // An address (an `lea`, or a label's) costs no more to make than to copy, so it moves
            // only to feed what moved with it, never to be held in a register through the loop
            // for what stayed. So does a copy: a load whose value the rewrite found is a copy of
            // a value from outside the loop, and moving it lets what reads it move too. Each one
            // that something left in the loop still reads goes back, and with it whatever reads
            // it.
            if (self.hOrder.len() > before) { self.keepAddresses(p, k, before); }
            kept: long = 0;
            for z in before..self.hOrder.len() { if (self.hLoop.get(z) == k) { kept = kept + 1; } }
            if (kept > 0) {
                planned = planned + kept;
                if (jumps) { spare = spare - 1; self.lpLabel.set(k, 0); }
            }
        }
        if (planned == 0) { return; }
        self.nHoisted = self.nHoisted + planned;
        // The new labels, and the entry jumps sent to them.
        drop: long = 0;
        for k in 0..nl {
            if (self.lpLabel.get(k) < 0) { continue; }
            self.phSeq = self.phSeq + 1;
            lab: Sym = madeName(".PH", self.phSeq, "");
            self.lpLabel.set(k, lab as long);
            drop = drop + 1;
            h: long = self.lpHead.get(k);
            for z in 0..self.lpCount.get(k) { self.blockMark.set(self.lpList.get(self.lpFirst.get(k) + z), k); }
            pf: long = self.predFirst.get(h);
            for e in 0..self.predCount.get(h) {
                u: long = self.predBlock.get(pf + e);
                if (!self.reach.get(u) || self.predKind.get(pf + e) != E_TAKEN || self.loopHas(k, u)) { continue; }
                last: long = self.lastReal(p, u);
                if (last < 0) { continue; }
                j: Instr = p.code.get(self.first + last);
                j.name = lab;
                p.code.set(self.first + last, j);
            }
        }
        // The run rewritten, as long as it was: each preheader before its header's label.
        fillLong(&self.hAt, self.n, -1);
        for k in 0..nl { self.hAt.set(self.bStart.get(self.lpHead.get(k)), k); }
        self.hBuf.clear();
        for i in 0..self.n {
            ix: long = self.first + i;
            k: long = self.hAt.get(i);
            if (k >= 0) {
                if (self.lpLabel.get(k) >= 0) {
                    lb: Instr = instr(IROp.Label);
                    lb.name = self.lpLabel.get(k) as Sym;
                    self.hBuf.push(lb);
                }
                for z in 0..self.hOrder.len() {
                    if (self.hLoop.get(z) == k) { self.hBuf.push(p.code.get(self.first + self.hOrder.get(z))); }
                }
            }
            if (self.hMoved.get(i)) { continue; }
            if (drop > 0 && p.code[ix].op == IROp.Nop) { drop = drop - 1; continue; }
            self.hBuf.push(p.code.get(ix));
        }
        while (self.hBuf.len() < self.n) { self.hBuf.push(instr(IROp.Nop)); }
        for i in 0..self.n { p.code.set(self.first + i, self.hBuf.get(i)); }
    }

    // Whether a load moved out of loop `k` this round (from `before` on) reads what load `i` does,
    // through operands no move of this round made: then `i` becomes a copy of it, moved with it.
    sameHoisted &self inout p:IRProgram i:long k:long before:long -> void {
        ix: long = self.first + i;
        in: Instr = p.code.get(ix);
        if ((in.op != IROp.PtrLoad && in.op != IROp.Load) || in.dst == NO_TEMP) { return; }
        if (self.movedSince(p, in.a, k, before) || self.movedSince(p, in.x, k, before)) { return; }
        for z in before..self.hOrder.len() {
            if (self.hLoop.get(z) != k) { continue; }
            j: Instr = p.code.get(self.first + self.hOrder.get(z));
            if (j.op != in.op || j.kind != in.kind || j.a != in.a || j.x != in.x || j.scale != in.scale
                || j.imm != in.imm || j.name != in.name || j.isGlobal != in.isGlobal || j.dst == NO_TEMP) { continue; }
            mv: Instr = instr(IROp.Mov);
            mv.dst = in.dst;
            mv.a = j.dst;
            mv.kind = in.kind;
            mv.structName = in.structName;
            p.code.set(ix, mv);
            return;
        }
    }

    // Whether temp `t` is what a move out of loop `k` this round (from `before` on) defines.
    movedSince &self inout p:IRProgram t:Temp k:long before:long -> bool {
        if (t == NO_TEMP) { return false; }
        for z in before..self.hOrder.len() {
            if (self.hLoop.get(z) != k) { continue; }
            at: long = self.hOrder.get(z);
            if (p.code[self.first + at].dst == t) { return true; }
        }
        return false;
    }

    // Loop `k`'s moves from `before` on, minus each address that something left in the loop still
    // reads, and (to a fixpoint) whatever reads one that went back. A read outside the loop does
    // not count: on a cold path to a panic, say, it holds no register through the loop's trips.
    keepAddresses &self inout p:IRProgram k:long before:long -> void {
        fillLong(&self.hUse, self.nt, 0);
        for z in 0..self.lpCount.get(k) {
            b: long = self.lpList.get(self.lpFirst.get(k) + z);
            for i in self.bStart.get(b)..self.stopOf(b) { if (!self.hMoved.get(i)) { self.countReads(p, i); } }
        }
        going: bool = true;
        while (going) {
            going = false;
            for z in before..self.hOrder.len() {
                if (self.hLoop.get(z) != k) { continue; }
                i: long = self.hOrder.get(z);
                ix: long = self.first + i;
                o: IROp = p.code[ix].op;
                back: bool = false;
                if (o == IROp.AddrOf || o == IROp.StrAddr || o == IROp.FnAddr || o == IROp.VtableAddr || o == IROp.Mov) {
                    back = self.hUse.get(self.rel(p.code[ix].dst)) > 0;
                }
                if (!back && !self.outsideLoop(p.code[ix].a, k)) { back = true; }
                if (!back && !p.code[ix].bIsImm && !self.outsideLoop(p.code[ix].b, k)) { back = true; }
                if (!back) { continue; }
                self.hMoved.set(i, false);
                self.hLoop.set(z, -1);
                self.lpDef.set(self.rel(p.code[ix].dst), k);
                self.countReads(p, i);
                going = true;
            }
        }
    }
    // What instruction `i` reads, counted into `hUse`.
    countReads &self inout p:IRProgram i:long -> void {
        ix: long = self.first + i;
        o: IROp = p.code[ix].op;
        if (o == IROp.Nop || o == IROp.Label) { return; }
        self.addUse(p.code[ix].a);
        if (!p.code[ix].bIsImm) { self.addUse(p.code[ix].b); }
        na: long = p.code[ix].argCount;
        if (na > 0) { fa: long = p.code[ix].firstArg; for k in 0..na { self.addUse(p.args.get(fa + k)); } }
        np: long = p.code[ix].pieceCount;
        if (np > 0) { fp: long = p.code[ix].firstPiece; for k in 0..np { self.addUse(p.asmVals.get(fp + k)); } }
    }
    addUse &self t:Temp -> void {
        r: long = self.rel(t);
        if (r >= 0) { self.hUse.set(r, self.hUse.get(r) + 1); }
    }

    // Whether `t` holds an address in the frame or a global's: an address constant
    // (`addressConstants`), seen through copies of one (a closure's capture is a copy of `&x`).
    frameAddress &self inout p:IRProgram t0:Temp -> bool {
        t: Temp = t0;
        steps: long = 0;
        while (steps < 8) {
            r: long = self.rel(t);
            if (r < 0) { return false; }
            if (self.acRoot.get(r) >= 0) { return true; }
            if (self.defs.get(r) != 1 || self.defAt.get(r) < 0) { return false; }
            d: long = self.first + self.defAt.get(r);
            if (p.code[d].op != IROp.Mov) { return false; }
            t = p.code[d].a;
            steps = steps + 1;
        }
        return false;
    }

    // Whether block `b` is one of loop `k`'s.
    loopHas &self k:long b:long -> bool {
        for z in 0..self.lpCount.get(k) { if (self.lpList.get(self.lpFirst.get(k) + z) == b) { return true; } }
        return false;
    }

    // Instruction `i` of loop `k` (header `h`), moved out: see `hoist`.
    canHoist &self inout p:IRProgram i:long h:long k:long -> bool {
        ix: long = self.first + i;
        o: IROp = p.code[ix].op;
        if (o == IROp.Nop || o == IROp.Label) { return false; }
        r: long = self.rel(p.code[ix].dst);
        if (r < 0 || self.defs.get(r) != 1) { return false; }
        if (p.code[ix].argCount > 0 || p.code[ix].pieceCount > 0 || p.code[ix].paramSeed) { return false; }
        kd: Lit = p.code[ix].kind;
        // A constant is made again where it is read, but one past 32 bits takes a ten-byte move each
        // time: made once before the loop, it may keep a register instead (`markRemat` still lets it
        // go where none is free).
        wideConst: bool = o == IROp.Const && !isFloatKind(kd) && !gWideConstOff
                          && (p.code[ix].imm < IMM_LO || p.code[ix].imm > IMM_HI);
        if (!wideConst && !hoistableOp(o, kd, p.code[ix].bIsImm, p.code[ix].bImm)) { return false; }
        // Not a float: seven `xmm` registers are all a loop has for its floats, and a value hoisted
        // into one for the whole loop pushes the loop's own floats into general registers
        // (measured: the Mandelbrot kernel ran 9% slower). Recomputing it each trip is cheaper.
        if (isFloatKind(kd) || (o == IROp.Convert && (isFloatKind(p.code[ix].fromKind) || isFloatKind(p.code[ix].toKind)))) { return false; }
        if (!self.outsideLoop(p.code[ix].a, k)) { return false; }
        if (!p.code[ix].bIsImm && !self.outsideLoop(p.code[ix].b, k)) { return false; }
        if (o == IROp.PtrLoad || o == IROp.Load) { return self.loadHoistable(p, i, h, k); }
        return true;
    }

    // An operand no instruction of loop `k` defines (or none left in it).
    outsideLoop &self t:Temp k:long -> bool {
        if (t == NO_TEMP) { return true; }
        r: long = self.rel(t);
        return r >= 0 && self.lpDef.get(r) != k;
    }

    // A load moved out of loop `k`: it may run where it did not, and nothing in the loop writes
    // what it reads.
    loadHoistable &self inout p:IRProgram i:long h:long k:long -> bool {
        l: long = self.instLoc.get(i);
        f0: long = self.instFact.get(i);
        if (l < 0 || f0 < 0) { return false; }
        ix: long = self.first + i;
        if (p.code[ix].op == IROp.PtrLoad) {
            a: Temp = p.code[ix].a;
            safe: bool = self.blockOf.get(i) == h || p.kindOf(a) == Lit.Ref || pairKind(p.kindOf(a)) || self.frameAddress(p, a);
            if (!safe) { return false; }
        }
        W: long = self.words;
        at: long = self.bits.len();
        for w in 0..W { self.bits.push(0); }
        written: bool = false;
        for z in 0..self.lpCount.get(k) {
            b: long = self.lpList.get(self.lpFirst.get(k) + z);
            for j in self.bStart.get(b)..self.stopOf(b) {
                oj: IROp = p.code[self.first + j].op;
                if (oj != IROp.PtrStore && oj != IROp.Store && oj != IROp.Call && oj != IROp.CallIndirect
                    && oj != IROp.Asm && oj != IROp.AggCopy && oj != IROp.AggZero && oj != IROp.ArrStore
                    && oj != IROp.Atomic && oj != IROp.MemCopy) { continue; }
                for w in 0..W { self.bits.set(at + w, 0); }
                self.touch(at, f0, 1);
                self.killMem(p, j, at, 0);
                if (!self.has(at, f0)) { written = true; }
                if (written) { break; }
            }
            if (written) { break; }
        }
        self.bits.truncate(at);
        return !written;
    }

    // Immediate dominators over the reachable blocks (Cooper, Harvey and Kennedy), in reverse
    // postorder.
    dominators &self -> void {
        nb: long = self.bStart.len();
        fillLong(&self.rpoNum, nb, -1);
        for oi in 0..self.order.len() { self.rpoNum.set(self.order.get(oi), oi); }
        fillLong(&self.idom, nb, -1);
        if (self.order.len() == 0) { return; }
        e: long = self.order.get(0);
        self.idom.set(e, e);
        changed: bool = true;
        while (changed) {
            changed = false;
            for oi in 1..self.order.len() {
                b: long = self.order.get(oi);
                nd: long = -1;
                pf: long = self.predFirst.get(b);
                for k in 0..self.predCount.get(b) {
                    u: long = self.predBlock.get(pf + k);
                    if (!self.reach.get(u) || self.idom.get(u) < 0) { continue; }
                    if (nd < 0) { nd = u; } else { nd = self.intersect(u, nd); }
                }
                if (nd >= 0 && self.idom.get(b) != nd) { self.idom.set(b, nd); changed = true; }
            }
        }
    }
    intersect &self a0:long b0:long -> long {
        a: long = a0;
        b: long = b0;
        while (a != b) {
            while (self.rpoNum.get(a) > self.rpoNum.get(b)) { a = self.idom.get(a); }
            while (self.rpoNum.get(b) > self.rpoNum.get(a)) { b = self.idom.get(b); }
        }
        return a;
    }
    // Whether block `a` dominates block `b` (both reachable).
    dominates &self a:long b0:long -> bool {
        b: long = b0;
        going: bool = true;
        while (going) {
            if (b == a) { return true; }
            nx: long = self.idom.get(b);
            if (nx < 0 || nx == b) { going = false; } else { b = nx; }
        }
        return false;
    }

    // ─── the graph ───────────────────────────────────────────────────────────

    buildBlocks &self inout p:IRProgram -> void {
        self.bStart.clear(); self.bEnd.clear(); self.bTaken.clear(); self.bFall.clear();
        self.bCond.clear(); self.bNeg.clear();
        if (self.labelAt.cap() > 512) { self.labelAt = map![]; } else { self.labelAt.clear(); }
        fillLong(&self.blockOf, self.n, -1);
        // Leaders: the first instruction, every label, whatever follows a transfer of control.
        startNext: bool = true;
        // Read in place: two fields of each instruction, not a copy of all of it.
        for i in 0..self.n {
            ix: long = self.first + i;
            o: IROp = p.code[ix].op;
            if (o == IROp.Label || startNext) {
                if (self.bStart.len() > 0) { self.bEnd.push(i - 1); }
                self.bStart.push(i);
                startNext = false;
            }
            b: long = self.bStart.len() - 1;
            self.blockOf.set(i, b);
            if (o == IROp.Label) { self.labelAt.put(p.code[ix].name as long, b); }
            if (isTerminator(o) || (o == IROp.Call && p.code[ix].noReturn)) { startNext = true; }
        }
        self.bEnd.push(self.n - 1);
        nb: long = self.bStart.len();
        for b in 0..nb {
            taken: long = -1;
            fall: long = -1;
            if (b + 1 < nb) { fall = b + 1; }
            last: long = self.lastReal(p, b);
            if (last >= 0) {
                lx: long = self.first + last;
                lo: IROp = p.code[lx].op;
                if (isBranch(lo)) {
                    hit: Option<long> = self.labelAt.find(p.code[lx].name as long);
                    match hit { Some(t) { taken = t; } None { } }
                    if (lo == IROp.Jmp) { fall = -1; }
                } else if (lo == IROp.Ret || lo == IROp.RetVoid || (lo == IROp.Call && p.code[lx].noReturn)) {
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
            if (p.code[self.first + i].op != IROp.Nop) { return i; }
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
                if (p.code[at].op != IROp.Nop) {
                    p.code.set(at, instr(IROp.Nop));
                    self.nUnreach = self.nUnreach + 1;
                }
            }
        }
    }

    // ─── jump threading ──────────────────────────────────────────────────────

    // A block that does nothing but branch (its label, then a `jz`, a `jcc` or a `jmp`) is
    // passed through by any edge into it that already decides where it goes: the predecessor
    // jumps straight to the branch's target, or to what follows the block. An edge decides the
    // branch when the tested temp's last definition before it is a constant, or when the
    // predecessor's own branch tested the same thing. The first is the bool an inlined predicate
    // hands back (`b = const 1; jmp .L` ahead of `.L: jz .M if !b`), which is what `?` through
    // `Try.isBreak` leaves. A `jmp` is decided by every edge.
    //
    // When every edge into a conditional block is decided, the block is rewritten in place, since
    // nothing can be inserted here. Its branch's slot becomes the label that the jumps to what
    // follows the block aim at, and the slot before that (its own label) becomes the `jmp` that a
    // fallthrough edge going to the taken target needs. The block then no longer reads the temp,
    // and the constants it tested die. This repeats while it finds something, a few rounds at
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
            o: IROp = p.code[self.first + i].op;
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
        // A block of nothing but its label goes on to the next one, so a jump into it may as well
        // name the next one's label, when it has one. That is done only where the next block is
        // itself just a jump, which this then skips; a label falling into another label names
        // the same address anyway.
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

    // ─── threading past a block that reads back what its predecessors stored ───────────

    // A join block that copies an aggregate into a frame slot, loads a field of it back and
    // branches on that field. `match look(n)` and `?` through `Try` make these: the callee's
    // result is built in two blocks that each store a constant tag, and the join tests the tag.
    // Every edge into such a block decides its branch, only not through a temp but through the
    // memory its predecessors wrote.
    //
    // An edge whose predecessor stored a constant there is pointed straight at the target the
    // constant picks. The constant is found by walking back through the join block and the
    // predecessor, and through block copies (`slotOnEdge`). This is done only when nothing the
    // target reaches touches a slot the join block writes (`slotsUnread`): the block's copies are
    // then dead on that path, and skipping them is what takes the second compare away. The other
    // edges keep the block, and the dataflow then decides it, forwarding the remaining
    // predecessor's stores through the copies (`mapCopies`).
    //
    // The block may hold only labels, slot addresses, block copies into frame slots no other code
    // can reach, copies and constants, and the load. Answers whether it moved an edge.
    threadPastSlots &self inout p:IRProgram -> bool {
        if (gThreadOff) { return false; }
        ready: bool = false;
        moved: bool = false;
        nb: long = self.bStart.len();
        for b in 1..nb {
            if (!self.reach.get(b)) { continue; }
            last: long = self.lastReal(p, b);
            if (last < 0) { continue; }
            bi: Instr = p.code.get(self.first + last);
            imm: long = 0;
            if (bi.op == IROp.Jcc) {
                if (isFloatKind(bi.kind) || bi.a == NO_TEMP) { continue; }
                imm = bi.bImm;
                if (!bi.bIsImm) {
                    if (!self.singleConst(p, bi.b)) { continue; }
                    imm = self.cv;
                }
            } else if (bi.op != IROp.Jz || bi.a == NO_TEMP) { continue; }
            tb: long = self.bTaken.get(b);
            fb: long = self.bFall.get(b);
            if (tb < 0 || fb < 0 || tb == b || fb == b || tb == fb) { continue; }
            // The body: what it may hold, the load the branch tests, nothing longer than a few.
            ld: long = -1;
            real: long = 0;
            ok: bool = true;
            for i in self.bStart.get(b)..last {
                o: IROp = p.code[self.first + i].op;
                if (o == IROp.Label || o == IROp.Nop) { continue; }
                real = real + 1;
                if (o != IROp.AddrOf && o != IROp.AggSlot && o != IROp.PtrLoad && o != IROp.AggCopy
                    && o != IROp.Mov && o != IROp.Const) { ok = false; break; }
                if (o == IROp.AddrOf && p.code[self.first + i].isGlobal) { ok = false; break; }
                if (p.code[self.first + i].dst == bi.a) { ld = i; }
            }
            if (!ok || ld < 0 || real > MAX_THREAD_BODY) { continue; }
            // Through copies made in the block: the value tested is the one loaded.
            hops: long = 0;
            while (p.code[self.first + ld].op == IROp.Mov && hops < 4) {
                src: Temp = p.code[self.first + ld].a;
                j: long = ld - 1;
                while (j >= self.bStart.get(b) && p.code[self.first + j].dst != src) { j = j - 1; }
                if (j < self.bStart.get(b)) { break; }
                ld = j;
                hops = hops + 1;
            }
            if (p.code[self.first + ld].op != IROp.PtrLoad) { continue; }
            // What the rewrites left unread goes first: a copy of the tested value the dataflow
            // made for a check it then decided would otherwise count as a reader. The slots'
            // addresses and what reaches them are the dataflow's own (`addressConstants`, from
            // before the rewrites, which moved no address).
            if (!ready) { self.sweep(p); ready = true; }
            li: Instr = p.code.get(self.first + ld);
            if (!self.privateSlot(li.a)) { continue; }
            root: long = self.acOf(li.a);
            // Every block copy the body makes lands in a private slot.
            for i in self.bStart.get(b)..last {
                in: Instr = p.code.get(self.first + i);
                if (in.op == IROp.AggCopy && !self.privateSlot(in.a)) { ok = false; break; }
            }
            if (!ok) { continue; }
            pf: long = self.predFirst.get(b);
            for k in 0..self.predCount.get(b) {
                if (self.predKind.get(pf + k) != E_TAKEN) { continue; }
                pb: long = self.predBlock.get(pf + k);
                if (pb == b || !self.reach.get(pb) || self.bTaken.get(pb) == self.bFall.get(pb)) { continue; }
                if (!self.slotOnEdge(p, b, ld, pb, root, self.acOff.get(self.rel(li.a)) + li.imm, kindWidth(li.kind))) { continue; }
                x: long = canon(li.kind, self.cv);
                taken: bool = x == 0;
                if (bi.op == IROp.Jcc) { taken = compareHolds(bi.cmpOp, canon(bi.kind, x), canon(bi.kind, imm), kindUnsigned(bi.kind)); }
                to: Sym = bi.name;
                tgt: long = tb;
                if (!taken) { to = self.entryLabel(p, fb); tgt = fb; }
                if (to == NO_SYM || !self.slotsUnread(p, b, last, tgt)) { continue; }
                self.retarget(p, pb, to);
                moved = true;
            }
        }
        return moved;
    }

    // A label for where code falling into block `b` goes: the block's own label, the label it
    // only jumps on to, or, past blocks of nothing but deleted instructions, the next block's.
    entryLabel &self inout p:IRProgram b0:long -> Sym {
        b: long = b0;
        for k in 0..4 {
            if (b < 0) { return NO_SYM; }
            l: Sym = self.labelOf(p, b);
            if (l != NO_SYM) { return l; }
            if (self.jumpOnly(p, b)) {
                j: long = self.first + self.lastReal(p, b);
                return self.forward(p, p.code[j].name);
            }
            if (self.lastReal(p, b) >= 0) { return NO_SYM; }
            b = self.bFall.get(b);
        }
        return NO_SYM;
    }

    // `t` is the address of a frame slot nothing but this function's loads, stores and block
    // copies reach: no call, no escape, no global.
    privateSlot &self t:Temp -> bool {
        r: long = self.rel(t);
        if (r < 0 || self.acRoot.get(r) < 0 || self.acKind.get(r) != R_SLOT) { return false; }
        return self.privateRoot(self.acRoot.get(r));
    }
    privateRoot &self root:long -> bool { return !self.exposed.has(root) && !self.lent.has(root); }

    // The constant last stored in the `width` bytes at `off` in frame slot `root`, as the edge
    // from `pb` into `b` leaves them just before `b`'s instruction `from`; it is left in `cv`. The
    // walk goes back through `b`, then through `pb` and its chain of single predecessors. A block
    // copy into the slot moves the question to the copy's source, and writes to other slots are
    // passed over, since the slot is private and nothing else reaches it.
    slotOnEdge &self inout p:IRProgram b:long from:long pb0:long root0:long off0:long width:long -> bool {
        root: long = root0;
        off: long = off0;
        blk: long = b;
        i: long = from - 1;
        steps: long = 0;
        while (steps < 8) {
            s: long = self.bStart.get(blk);
            while (i >= s) {
                in: Instr = p.code.get(self.first + i);
                o: IROp = in.op;
                if (o == IROp.Asm || o == IROp.Atomic || o == IROp.MemCopy) { return false; }
                if ((o == IROp.Store || o == IROp.ArrStore) && in.name != NO_SYM && !in.isGlobal && (in.name as long) == root) { return false; }
                if (o == IROp.AggZero) {
                    ar: long = self.rel(in.a);
                    if (ar >= 0 && self.acRoot.get(ar) == root) {
                        lo: long = self.acOff.get(ar);
                        if (off >= lo && off + width <= lo + in.imm) { self.cv = 0; return true; }
                        if (off < lo + in.imm && lo < off + width) { return false; }
                    }
                } else if (o == IROp.PtrStore) {
                    ar: long = self.rel(in.a);
                    if (ar >= 0 && self.acRoot.get(ar) == root) {
                        lo: long = self.acOff.get(ar) + in.imm;
                        w: long = kindWidth(in.kind);
                        if (lo == off && w == width) {
                            if (in.bIsImm) { self.cv = in.bImm; return true; }
                            return self.constBefore(p, blk, i, in.b);
                        }
                        if (off < lo + w && lo < off + width) { return false; }
                    }
                } else if (o == IROp.AggCopy) {
                    ar: long = self.rel(in.a);
                    if (ar >= 0 && self.acRoot.get(ar) == root) {
                        lo: long = self.acOff.get(ar);
                        if (off >= lo && off + width <= lo + in.imm) {
                            if (!self.privateSlot(in.b)) { return false; }
                            br: long = self.rel(in.b);
                            off = off - lo + self.acOff.get(br);
                            root = self.acRoot.get(br);
                        } else if (off < lo + in.imm && lo < off + width) { return false; }
                    }
                }
                i = i - 1;
            }
            if (steps == 0) { blk = pb0; }
            else {
                if (blk == 0 || self.predCount.get(blk) != 1) { return false; }
                blk = self.predBlock.get(self.predFirst.get(blk));
            }
            i = self.bEnd.get(blk);
            steps = steps + 1;
        }
        return false;
    }

    // Whether `t` is a constant where instruction `at` of block `blk` reads it: its one
    // definition is a `Const`, or its last definition before `at` in the block is one.
    constBefore &self inout p:IRProgram blk:long at:long t:Temp -> bool {
        if (self.singleConst(p, t)) { return true; }
        i: long = at - 1;
        while (i >= self.bStart.get(blk)) {
            in: Instr = p.code.get(self.first + i);
            if (in.op != IROp.Nop && in.dst == t) {
                if (in.op != IROp.Const) { return false; }
                self.cv = in.imm;
                return true;
            }
            i = i - 1;
        }
        return false;
    }

    // Whether the blocks reachable from `t` leave alone everything block `b` makes before `last`:
    // none of them touches a slot one of `b`'s block copies writes, none reads a temp `b` defines,
    // and none is `b` itself. What `b` does is then dead on any path that goes to `t`.
    slotsUnread &self inout p:IRProgram b:long last:long t:long -> bool {
        self.tWritten.clear();
        self.tDefs.clear();
        for i in self.bStart.get(b)..last {
            if (p.code[self.first + i].op == IROp.AggCopy) { self.tWritten.push(self.acOf(p.code[self.first + i].a)); }
            if (p.code[self.first + i].dst != NO_TEMP) { self.tDefs.push(p.code[self.first + i].dst); }
        }
        nb: long = self.bStart.len();
        fillBool(&self.tSeen, nb, false);
        self.tStack.clear();
        self.tStack.push(t);
        self.tSeen.set(t, true);
        while (self.tStack.len() > 0) {
            x: long = self.tStack.pop();
            if (x == b) { return false; }
            for i in self.bStart.get(x)..self.stopOf(x) {
                o: IROp = p.code[self.first + i].op;
                if (o == IROp.Nop || o == IROp.Label) { continue; }
                in: Instr = p.code.get(self.first + i);
                if (in.name != NO_SYM && !in.isGlobal && (o == IROp.Load || o == IROp.Store
                    || o == IROp.ArrLoad || o == IROp.ArrStore) && self.writtenBy(in.name as long)) { return false; }
                // An address of one is a read only where it is used (asked of the operands below),
                // as long as the temp holding it is one those questions can follow.
                if (o == IROp.AddrOf && !in.isGlobal && self.writtenBy(in.name as long) && self.acOf(in.dst) < 0) { return false; }
                if (o == IROp.AggSlot && self.writtenBy(AGG_BASE + in.imm) && self.acOf(in.dst) < 0) { return false; }
                if (self.writtenBy(self.acOf(in.a)) || (!in.bIsImm && self.writtenBy(self.acOf(in.b)))) { return false; }
                if (self.defdIn(in.a) || (!in.bIsImm && self.defdIn(in.b))) { return false; }
                for k in 0..in.argCount {
                    t: Temp = p.args.get(in.firstArg + k);
                    if (self.writtenBy(self.acOf(t)) || self.defdIn(t)) { return false; }
                }
                for k in 0..in.pieceCount { if (self.defdIn(p.asmVals.get(in.firstPiece + k))) { return false; } }
            }
            nx: long = self.bTaken.get(x);
            if (nx >= 0 && !self.tSeen.get(nx)) { self.tSeen.set(nx, true); self.tStack.push(nx); }
            nx = self.bFall.get(x);
            if (nx >= 0 && !self.tSeen.get(nx)) { self.tSeen.set(nx, true); self.tStack.push(nx); }
        }
        return true;
    }
    defdIn &self t:Temp -> bool {
        if (t == NO_TEMP) { return false; }
        for k in 0..self.tDefs.len() { if (self.tDefs.get(k) == t) { return true; } }
        return false;
    }
    writtenBy &self root:long -> bool {
        if (root < 0) { return false; }
        for k in 0..self.tWritten.len() { if (self.tWritten.get(k) == root) { return true; } }
        return false;
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
            if (p.code[self.first + i].dst == t) {
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
                o: IROp = p.code[self.first + i].op;
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
            o: IROp = p.code[self.first + i].op;
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
        if (self.lent.cap() > 512) { self.lent = map![]; } else { self.lent.clear(); }
        fillLong(&self.callFx, self.n, -1);
        for i in 0..self.n {
            r: long = self.rel(p.code[self.first + i].dst);
            if (r < 0 || self.defs.get(r) != 1) { continue; }
            in: Instr = p.code.get(self.first + i);
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
            } else if (in.op != IROp.Mov && !addressConvert(in)) { continue; }
            self.acRoot.set(r, self.acRoot.get(ar));
            self.acKind.set(r, self.acKind.get(ar));
            self.acOff.set(r, self.acOff.get(ar) + k);
        }
        for i in 0..self.n {
            o: IROp = p.code[self.first + i].op;
            if (o == IROp.Nop || o == IROp.Label) { continue; }
            in: Instr = p.code.get(self.first + i);
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
            // A direct call whose callee's summary is known: an address handed to a parameter
            // that does not escape is lent for the call, and exposes nothing.
            if (o == IROp.Call) {
                s: long = fxOfCallee(p, in.name);
                if (s >= 0 && fxParams(s) == in.argCount) {
                    self.callFx.set(i, s);
                    lends: bool = false;
                    for k in 0..in.argCount {
                        t: Temp = p.args.get(in.firstArg + k);
                        if (fxEscapes(s, k)) { self.expose(t); }
                        else if (self.acOf(t) >= 0) { self.lent.put(self.acOf(t), true); lends = true; }
                    }
                    if (lends) { self.nLentCalls = self.nLentCalls + 1; }
                    continue;
                }
            }
            // A call whose callee's summary is not known but whose conventions are: what a parameter
            // it is lent takes is never kept (in safe code a borrow dies with its call), so the slot
            // is lent, not exposed, whatever the callee does with the rest.
            if ((o == IROp.Call || o == IROp.CallIndirect) && (in.imm & CALL_KNOWN) != 0 && !gLentOff) {
                lends: bool = false;
                for k in 0..in.argCount {
                    t: Temp = p.args.get(in.firstArg + k);
                    if (!callLends(in.imm, k)) { self.expose(t); }
                    else if (self.acOf(t) >= 0) { self.lent.put(self.acOf(t), true); lends = true; }
                }
                if (o == IROp.CallIndirect) { self.expose(in.a); }
                if (lends) { self.nLentCalls = self.nLentCalls + 1; }
                continue;
            }
            if ((o == IROp.Add || o == IROp.Mov || o == IROp.Convert) && self.acOf(in.dst) >= 0) { continue; }
            self.expose(in.a);
            if (!in.bIsImm) { self.expose(in.b); }
            for k in 0..in.argCount { self.expose(p.args.get(in.firstArg + k)); }
            for k in 0..in.pieceCount { self.expose(p.asmVals.get(in.firstPiece + k)); }
        }
    }

    // Which borrowed parameter each temp may be an address into (`bpMask`, `bpOther`), to a
    // fixpoint over its definitions: the parameter's seed, a read of its slot by name, and a
    // copy, conversion, sum or difference of those. An address plus an integer stays in the
    // object the address is in, the rule C's aliasing rests on too. Anything else (a load, a
    // call's result, a global's or a slot's address) is `bpOther`, and some of it may still point
    // into a parameter: what other arithmetic makes of one (a mask, a shift), and a call's result,
    // which carries each argument whose parameter the callee may hand back. Nothing is tracked in
    // a function declared `unsafe`, which may hand what it is lent anywhere.
    borrowProvenance &self inout p:IRProgram -> void {
        self.bpParam.clear();
        fillLong(&self.bpMask, self.nt, 0);
        fillBool(&self.bpOther, self.nt, false);
        self.bpLeak = 0;
        if (self.fnUnsafe || self.fnBorrows == 0 || gRestrictOff) { return; }
        names: Vec<Sym>;
        k: long = 0;
        i: long = 0;
        while (i < self.n && k < 62) {
            ix: long = self.first + i;
            if (p.code[ix].op != IROp.Load || !p.code[ix].paramSeed) { break; }
            if ((self.fnBorrows & (1 << k)) != 0 && p.code[ix].kind == Lit.Ref) {
                r: long = self.rel(p.code[ix].dst);
                if (r >= 0) { self.bpMask.set(r, self.bpMask.get(r) | (1 << self.bpParam.len())); }
                self.bpParam.push(k);
                names.push(p.code[ix].name);
            }
            k = k + 1;
            i = i + 1;
        }
        if (self.bpParam.len() == 0) { return; }
        seeds: long = i;
        // A parameter's slot written other than by its seed holds something else from then on.
        written: long = 0;
        for j in seeds..self.n {
            o: IROp = p.code[self.first + j].op;
            if (o != IROp.Store && o != IROp.AddrOf && o != IROp.ArrStore) { continue; }
            if (p.code[self.first + j].isGlobal) { continue; }
            nm: Sym = p.code[self.first + j].name;
            for q in 0..names.len() { if (names.get(q) == nm) { written = written | (1 << q); } }
        }
        // In order, so a pass is the fixpoint unless something read a temp before a definition of
        // it changed (a loop's, or a temp defined twice): `bpRead` says in which pass each was read.
        fillLong(&self.bpRead, self.nt, 0);
        rounds: long = 0;
        going: bool = true;
        while (going) {
            if (rounds >= 12) { self.bpParam.clear(); fillLong(&self.bpMask, self.nt, 0); return; }
            rounds = rounds + 1;
            going = false;
            // What leaks is read off the round that changed nothing, so with the provenance final.
            lk: long = 0;
            for j in seeds..self.n {
                ix: long = self.first + j;
                o: IROp = p.code[ix].op;
                if (o == IROp.PtrStore || o == IROp.ArrStore || o == IROp.Store || o == IROp.Call || o == IROp.CallIndirect
                    || o == IROp.Asm || o == IROp.Atomic) { lk = lk | self.leakAt(p, ix, j, rounds); }
                r: long = self.rel(p.code[ix].dst);
                if (r < 0 || o == IROp.Nop || o == IROp.Const) { continue; }
                m: long = 0;
                other: bool = false;
                if (o == IROp.Load) {
                    other = true;
                    if (!p.code[ix].isGlobal) {
                        for q in 0..names.len() {
                            if (names.get(q) == p.code[ix].name && (written & (1 << q)) == 0) { m = 1 << q; other = false; }
                        }
                    }
                } else if (o == IROp.Mov || o == IROp.Convert) {
                    self.bpReadAt(p.code[ix].a, rounds);
                    m = self.bpOf(p.code[ix].a);
                    other = self.bpElse(p.code[ix].a);
                } else if (o == IROp.Add || o == IROp.Sub) {
                    self.bpReadAt(p.code[ix].a, rounds);
                    if (!p.code[ix].bIsImm) { self.bpReadAt(p.code[ix].b, rounds); }
                    ma: long = self.bpOf(p.code[ix].a);
                    oa: bool = self.bpElse(p.code[ix].a);
                    mb: long = 0;
                    ob: bool = false;
                    if (!p.code[ix].bIsImm) { mb = self.bpOf(p.code[ix].b); ob = self.bpElse(p.code[ix].b); }
                    if (ma != 0 && mb == 0) { m = ma; other = oa; }
                    else if (mb != 0 && ma == 0) { m = mb; other = ob; }
                    else { m = ma | mb; other = oa || ob; }
                } else if (o == IROp.Call || o == IROp.CallIndirect) {
                    // A result may be an address into what the callee was handed and hands back.
                    other = true;
                    s: long = -1;
                    if (o == IROp.Call) { s = self.callFx.get(j); }
                    fa: long = p.code[ix].firstArg;
                    for q in 0..p.code[ix].argCount {
                        if (s >= 0 && !fxRet(s, q)) { continue; }
                        if (s < 0 && !resultHoldsAddress(p.code[ix].kind)) { break; }
                        at: Temp = p.args.get(fa + q);
                        self.bpReadAt(at, rounds);
                        m = m | self.bpOf(at);
                    }
                } else {
                    other = true;
                    // Whatever else an address goes through (a mask, a shift), what comes out may
                    // still point where it pointed.
                    if (o == IROp.Mul || o == IROp.Div || o == IROp.Mod || o == IROp.BAnd || o == IROp.BOr
                        || o == IROp.BXor || o == IROp.Shl || o == IROp.Shr || o == IROp.BNot) {
                        self.bpReadAt(p.code[ix].a, rounds);
                        m = self.bpOf(p.code[ix].a);
                        if (!p.code[ix].bIsImm && p.code[ix].b != NO_TEMP) {
                            self.bpReadAt(p.code[ix].b, rounds);
                            m = m | self.bpOf(p.code[ix].b);
                        }
                    }
                }
                grew: bool = false;
                if ((self.bpMask.get(r) | m) != self.bpMask.get(r)) { self.bpMask.set(r, self.bpMask.get(r) | m); grew = true; }
                if (other && !self.bpOther.get(r)) { self.bpOther.set(r, true); grew = true; }
                if (grew && self.bpRead.get(r) == rounds) { going = true; }
            }
            self.bpLeak = lk;
        }
    }

    // The borrowed parameters of which this function puts a derived address where the provenance
    // above loses it: stored anywhere (a frame slot too, read back as a pointer of no known
    // origin), or handed to a callee that keeps it, to `asm` or to an atomic. A write through such
    // a pointer, or a call that writes what it was not handed, may then reach their bytes.
    // Instruction `ix` (relative `j`), one of those: the parameters it leaks. What it reads counts
    // as read in this pass, so that a later definition growing it makes another pass.
    leakAt &self inout p:IRProgram ix:long j:long pass:long -> long {
        o: IROp = p.code[ix].op;
        lk: long = 0;
        if (o == IROp.PtrStore || o == IROp.ArrStore) {
            if (!p.code[ix].bIsImm) { lk = self.bpRd(p.code[ix].b, pass); }
        } else if (o == IROp.Store) {
            lk = self.bpRd(p.code[ix].a, pass);
        } else if (o == IROp.Call || o == IROp.CallIndirect) {
            s: long = -1;
            if (o == IROp.Call) { s = self.callFx.get(j); }
            fa: long = p.code[ix].firstArg;
            for q in 0..p.code[ix].argCount {
                if (s >= 0 && !fxKept(s, q)) { continue; }
                if (s < 0 && !gLentOff && callLends(p.code[ix].imm, q)) { continue; }
                lk = lk | self.bpRd(p.args.get(fa + q), pass);
            }
        } else {
            lk = self.bpRd(p.code[ix].a, pass);
            if (!p.code[ix].bIsImm) { lk = lk | self.bpRd(p.code[ix].b, pass); }
            for q in 0..p.code[ix].argCount { lk = lk | self.bpRd(p.args.get(p.code[ix].firstArg + q), pass); }
            for q in 0..p.code[ix].pieceCount { lk = lk | self.bpRd(p.asmVals.get(p.code[ix].firstPiece + q), pass); }
        }
        return lk;
    }
    bpRd &self t:Temp pass:long -> long {
        self.bpReadAt(t, pass);
        return self.bpOf(t);
    }
    bpReadAt &self t:Temp pass:long -> void {
        r: long = self.rel(t);
        if (r >= 0 && r < self.bpRead.len()) { self.bpRead.set(r, pass); }
    }
    bpOf &self t:Temp -> long {
        r: long = self.rel(t);
        if (r < 0 || r >= self.bpMask.len()) { return 0; }
        return self.bpMask.get(r);
    }
    bpElse &self t:Temp -> bool {
        r: long = self.rel(t);
        if (r < 0 || r >= self.bpOther.len()) { return t != NO_TEMP; }
        return self.bpOther.get(r);
    }
    // The borrowed parameter (its entry in `bpParam`) temp `t` is an address into and nothing
    // else, or -1.
    ownerOf &self t:Temp -> long {
        m: long = self.bpOf(t);
        if (m == 0 || (m & (m - 1)) != 0 || self.bpElse(t)) { return -1; }
        j: long = 0;
        while ((m & (1 << j)) == 0) { j = j + 1; }
        return j;
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
        self.borrowProvenance(p);
        self.roSeen.clear();
        self.fKind.clear(); self.fOp.clear(); self.fA.clear(); self.fB.clear(); self.fImm.clear();
        self.fIsImm.clear(); self.fUns.clear(); self.fLoc.clear(); if (self.factKey.cap() > 512) { self.factKey = map![]; } else { self.factKey.clear(); }
        self.lRootKind.clear(); self.lRoot.clear(); self.lOff.clear(); self.lWidth.clear(); self.lCls.clear();
        if (self.locKey.cap() > 512) { self.locKey = map![]; } else { self.locKey.clear(); }
        if (self.rootKey.cap() > 512) { self.rootKey = map![]; } else { self.rootKey.clear(); } self.rRk.clear(); self.rRoot.clear(); self.rootHead.clear();
        fillLong(&self.tempRootAt, self.nt, -1);
        self.locNext.clear(); self.locFactHead.clear(); self.factNext.clear();
        fillLong(&self.instLoc, self.n, -1);
        fillLong(&self.instFact, self.n, -1);
        self.copies.clear();
        self.needNonneg = false;
        nb: long = self.bStart.len();
        for i in 0..self.n {
            // Only these name a location or a fact: anything else is passed over before it is
            // copied out.
            o: IROp = p.code[self.first + i].op;
            if (o != IROp.PtrLoad && o != IROp.PtrStore && o != IROp.Load && o != IROp.Store && o != IROp.Bounds
                && o != IROp.AggCopy && o != IROp.Div && o != IROp.Mod) { continue; }
            if (!self.reach.get(self.blockOf.get(i))) { continue; }
            in: Instr = p.code.get(self.first + i);
            if (o == IROp.PtrLoad && in.dst != NO_TEMP && !isAggregate(in.kind)) {
                loc: long = self.locFor(in.a, in.imm, kindWidth(in.kind), loadClass(in.kind));
                self.instLoc.set(i, loc);
                // Not a global (see below) but a read-only one, and not `p = [p + 8]`, whose location moved
                // with it.
                if ((self.lRootKind.get(loc) != R_GLOBAL || self.isRo(self.lRoot.get(loc))) && !(self.lRootKind.get(loc) == R_TEMP && self.lRoot.get(loc) == in.dst)) {
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
                // write it between two plain reads, and a polling loop must see that. A read-only one
                // (`roGlobals`) holds what the compiler computed for the whole run.
                if (in.isGlobal) {
                    if (o == IROp.Load && in.dst != NO_TEMP && !isAggregate(in.kind) && self.isRo(in.name as long)) {
                        self.instFact.set(i, self.memFact(loc, in.dst));
                    }
                }
                else if (o == IROp.Load && in.dst != NO_TEMP && !isAggregate(in.kind)) {
                    self.instFact.set(i, self.memFact(loc, in.dst));
                } else if (o == IROp.Store && in.a != NO_TEMP) { self.instFact.set(i, self.memFact(loc, in.a)); }
            } else if (o == IROp.Bounds && in.a != NO_TEMP && in.b != NO_TEMP) {
                bop: IROp = IROp.CmpLt;
                if (in.imm != BOUNDS_INDEX) { bop = IROp.CmpLe; }
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
        self.joinCandidates(p);
        self.nf = self.fKind.len();
        if (self.nf == 0) { return false; }
        self.words = (self.nf + 63) / 64;
        if (nb * self.words * 64 > MAX_FLOW_BITS) { return false; }
        self.indexFacts(p);
        return true;
    }

    // A block copy carries what is known about its source to its destination: a field stored into
    // a struct being built, which is then copied into a local, reads back as the temp stored. For
    // each copy, each memory fact inside the source becomes a pair (the source fact, and the same
    // value at the destination), and the copy establishes the second wherever the first holds
    // just before it. This repeats, so a chain of copies (a callee's scratch, its result slot, the
    // local) carries a value all the way through. A block holding such a copy is solved by
    // walking it instruction by instruction (`bDyn`).
    mapCopies &self inout p:IRProgram -> void {
        nc: long = self.copies.len();
        fillLong(&self.cmFirst, nc, 0);
        fillLong(&self.cmCount, nc, 0);
        self.cmSrc.clear();
        self.cmDst.clear();
        self.bDyn.clear();
        for b in 0..self.bStart.len() { self.bDyn.push(false); }
        // Each copy's number by its instruction, where `step` asks it of every instruction.
        if (nc > 0) {
            fillLong(&self.copyAt, self.n, -1);
            for c in 0..nc { self.copyAt.set(self.copies.get(c), c); }
        }
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
                            if (self.fKind.get(f) != F_MEM) { f = self.factNext.get(f); continue; }
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
            r: long = -1;
            if (rk == R_TEMP) { r = self.rel(root); }
            if (r >= 0 && r < self.tempRootAt.len()) { self.tempRootAt.set(r, rid); }
            else { self.rootKey.put(mix(rk, root), rid); }
        }
        self.locNext.push(self.rootHead.get(rid));
        self.rootHead.set(rid, l);
        self.locFactHead.push(-1);
        return l;
    }

    // The locations relative to one root are a list, newest first, from `rootHead`.
    findRoot &self rk:long root:long -> long {
        if (rk == R_TEMP) {
            r: long = self.rel(root);
            if (r >= 0 && r < self.tempRootAt.len()) { return self.tempRootAt.get(r); }
        }
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
        // `c op b` with c constant is `b op' c`, the form the questions about one temp read.
        if (!isImm && b != NO_TEMP && a != NO_TEMP && !self.singleConst(p, b) && self.singleConst(p, a)) {
            t: Temp = a;
            a = b;
            b = t;
            op = swapCompare(op);
        }
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
        if (kind == F_MEM || kind == F_LREL) {
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
            if (self.fKind.get(f) != F_MEM && self.fKind.get(f) != F_LREL) { continue; }
            l: long = self.fLoc.get(f);
            rk: long = self.lRootKind.get(l);
            // What a read-only image holds is never written: no store, call or `asm` ends it.
            if (rk == R_GLOBAL && self.isRo(self.lRoot.get(l))) { continue; }
            if (rk == R_TEMP && self.roHere && self.roRootMemo(p, self.lRoot.get(l))) { continue; }
            setBit(&self.allMem, 0, f);
            if (rk != R_SLOT || self.exposed.has(self.lRoot.get(l))) { setBit(&self.callKill, 0, f); }
            if (rk == R_TEMP) { setBit(&self.tempMem, 0, f); }
        }
        // The facts about each borrowed parameter's own bytes, which only it reaches.
        // With none, `touchSet` reads what a call and a pointer end as they are.
        nbp: long = self.bpParam.len();
        if (nbp > 0) {
            fillLong(&self.ownSets, self.words * nbp, 0);
            fillLong(&self.callOther, self.words, 0);
            fillLong(&self.tempOther, self.words, 0);
            for f in 0..nf {
                if (self.fKind.get(f) != F_MEM && self.fKind.get(f) != F_LREL) { continue; }
                l: long = self.fLoc.get(f);
                if (self.lRootKind.get(l) != R_TEMP) { continue; }
                j: long = self.ownerOf(self.lRoot.get(l));
                if (j < 0) { continue; }
                setBit(&self.ownSets, j * self.words, f);
                // A parameter something got an address into reaches its bytes from anywhere:
                // its facts stay in what any call and any pointer end.
                if ((self.bpLeak & (1 << j)) != 0) { continue; }
                setBit(&self.tempOther, 0, f);
            }
            for w in 0..self.words {
                own: long = self.tempOther.get(w);
                self.callOther.set(w, self.callKill.get(w) & ~own);
                self.tempOther.set(w, self.tempMem.get(w) & ~own);
            }
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
            // A borrowed parameter's own bytes are reached only through what is derived from it, and
            // through it only those (and memory no name of this function reaches).
            own: long = self.ownerOf(root);
            if (own >= 0) { self.touchOwn(at, own, mode); self.touchSet(at, 4, mode); }
            else { self.touchSet(at, 3, mode); self.touchOwnOf(at, root, mode); }
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
        // A global named, or a slot of this frame, is never a borrowed parameter's own bytes: the
        // caller cannot lend this frame, and a global lent to the call is not named in it.
        if (rk == R_GLOBAL || self.exposed.has(root)) { self.touchSet(at, 4, mode); }
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

    // "Temp t holds `a op b`" is a fact like the others. The instruction computing it into t
    // establishes it, and a definition of t, a or b ends it (`forTemps` lists it under all
    // three). Where it holds on entry from every path, a second computation of the same
    // expression is a copy of t (`reuseExpr`). An expression is the operation, its operands (or
    // immediate), its type, and a conversion's two types. Computed again from the same temps it is
    // the same value, whatever the operation: a division that could fault has already run, on
    // every path here.
    //
    // Facts are made only for expressions that occur more than once. They are counted with their
    // operands seen through the expressions that define them (`shape`), so `p + i * 8` written
    // twice is found even when its `i * 8` was computed into two temps: the inner one becomes a
    // copy first, and the outer one's operands are then read through the copy (`resolve`).
    exprFacts &self inout p:IRProgram -> void {
        fillLong(&self.instExpr, self.n, -1);
        if (gCseOff) { return; }
        fillLong(&self.shapeOf, self.nt, 0);
        self.eOp.clear(); self.eA.clear(); self.eB.clear(); self.eImm.clear(); self.eIsImm.clear();
        self.eKind.clear(); self.eFrom.clear(); self.eTo.clear(); self.eHead.clear();
        if (self.eKey.cap() > 512) { self.eKey = map![]; } else { self.eKey.clear(); }
        if (self.shapeCount.cap() > 512) { self.shapeCount = map![]; } else { self.shapeCount.clear(); }
        // The dividends of a signed division by 2^k: a mask of one by 2^k - 1 gets its fact even
        // when it occurs once, since `lowBitsZero` asks for it.
        fillLong(&self.lowDiv, self.nt, 0);
        any: bool = false;
        for i in 0..self.n {
            ix: long = self.first + i;
            if (p.code[ix].op != IROp.Div || !p.code[ix].bIsImm || kindUnsigned(p.code[ix].kind)) { continue; }
            k: long = log2Exact(p.code[ix].bImm);
            r: long = self.rel(p.code[ix].a);
            if (k < 1 || r < 0) { continue; }
            self.lowDiv.set(r, self.lowDiv.get(r) | (1 << k));
            any = true;
        }
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
            if (!self.lowMask(in)) {
                hit: Option<long> = self.shapeCount.find(self.shape(in));
                match hit { Some(k) { if (k < 2) { continue; } } None { continue; } }
            }
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

    // `x & (2^k - 1)` where x is divided by 2^k somewhere (`lowDiv`).
    lowMask &self in:Instr -> bool {
        if (in.op != IROp.BAnd || !in.bIsImm || in.bImm < 1 || in.bImm >= IMM_HI) { return false; }
        k: long = log2Exact(in.bImm + 1);
        r: long = self.rel(in.a);
        return k >= 1 && r >= 0 && ((self.lowDiv.get(r) >> k) & 1) == 1;
    }

    // Whether x's low k bits are zero here: some temp holds `x & (2^k - 1)` (its fact, which a
    // write of either temp ends) and the facts here put it at zero, as the branch of `if (x % 2 ==
    // 0)` or `if ((x & 3) == 0)` leaves them. The mask is looked up at the division's own type.
    lowBitsZero &self inout p:IRProgram x:Temp k:long kd:Lit at:long -> bool {
        if (gCseOff) { return false; }
        g: long = self.exprGroupOf(IROp.BAnd, x, NO_TEMP, true, (1 << k) - 1, kd, Lit.Void, Lit.Void, false);
        if (g < 0) { return false; }
        f: long = self.eHead.get(g);
        while (f >= 0) {
            if (self.has(at, f) && self.decide(p, IROp.CmpEq, self.fA.get(f), NO_TEMP, true, 0, false, at) == 1) { return true; }
            f = self.eNext.get(f);
        }
        return false;
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

    // ─── relations made at a join ────────────────────────────────────────────
    //
    // A temp given a value on each of two paths and read where they meet (`n = x.len; if (y.len
    // < n) { n = y.len; }`) is known nowhere by the plain meet: each path's write of it ends
    // every fact about it, so nothing about it holds on entry from both. What does hold is a
    // relation each path makes true as it writes the temp, and that is what these are.
    //
    // A candidate is `t <= [loc]` for each load into a temp written more than once (`t = [loc]`
    // puts t at loc's value), and `t <= s` for each copy into one (`t = s`). At a join, a
    // candidate the meet left out holds on entry when it holds at the end of every edge into the
    // block (`holdsOnEdge`): the edge already carries it, or the edge's block writes t last of
    // all with a load or a copy, and the relation, read with t's new value, holds of the facts
    // just before that write. A relation proved that way is true when control leaves the block,
    // so it is a fact on entry like any other, and ends as one does: at a write of t, of the
    // other temp, or of the location.
    joinCandidates &self inout p:IRProgram -> void {
        nb: long = self.bStart.len();
        self.jcList.clear();
        fillLong(&self.jcFirst, nb, 0);
        fillLong(&self.jcCount, nb, 0);
        // Each temp's facts against a constant, chained by temp, so that a copy into a temp
        // written more than once can hand them on (`t = s` makes `s >= 0` a candidate `t >= 0`).
        fillLong(&self.jcImmHead, self.nt, -1);
        self.jcImmNext.clear();
        for f in 0..self.fKind.len() {
            self.jcImmNext.push(-1);
            if (self.fKind.get(f) != F_REL || !self.fIsImm.get(f)) { continue; }
            r: long = self.rel(self.fA.get(f));
            if (r < 0) { continue; }
            self.jcImmNext.set(f, self.jcImmHead.get(r));
            self.jcImmHead.set(r, f);
        }
        // Handed on first, in program order, so a copy of a copy (`i = from` then `k = i`) finds
        // what the first copy made.
        for i in 0..self.n {
            if (p.code[self.first + i].op != IROp.Mov || !self.reach.get(self.blockOf.get(i))) { continue; }
            in: Instr = p.code.get(self.first + i);
            r: long = self.rel(in.dst);
            if (r < 0 || self.defs.get(r) < 2 || in.a == NO_TEMP || in.a == in.dst || self.rel(in.a) < 0
                || isFloatKind(in.kind) || isAggregate(in.kind)) { continue; }
            g: long = self.jcImmHead.get(self.rel(in.a));
            while (g >= 0) {
                h: long = self.addFact(F_REL, self.fOp.get(g), in.dst, NO_TEMP, self.fImm.get(g), true, self.fUns.get(g), -1);
                if (h >= self.jcImmNext.len()) {
                    while (self.jcImmNext.len() <= h) { self.jcImmNext.push(-1); }
                    self.jcImmNext.set(h, self.jcImmHead.get(r));
                    self.jcImmHead.set(r, h);
                }
                g = self.jcImmNext.get(g);
            }
        }
        for b in 0..nb {
            if (!self.reach.get(b)) { continue; }
            self.jcFirst.set(b, self.jcList.len());
            for i in self.bStart.get(b)..self.stopOf(b) {
                o: IROp = p.code[self.first + i].op;
                if (o != IROp.PtrLoad && o != IROp.Load && o != IROp.Mov && o != IROp.Add) { continue; }
                in: Instr = p.code.get(self.first + i);
                r: long = self.rel(in.dst);
                if (r < 0 || self.defs.get(r) < 2 || in.paramSeed || isFloatKind(in.kind) || isAggregate(in.kind)) { continue; }
                uns: bool = kindUnsigned(p.kindOf(in.dst));
                f: long = -1;
                // A copy, or a counter's step: each of t's facts against a constant is a
                // candidate wherever this block leads (`immHolds` says whether it holds).
                if (o == IROp.Mov || (o == IROp.Add && in.a == in.dst && in.bIsImm && in.bImm == 1)) {
                    g: long = self.jcImmHead.get(r);
                    while (g >= 0) { self.jcList.push(g); g = self.jcImmNext.get(g); }
                }
                if (o == IROp.Add) { continue; }
                if (o == IROp.Mov) {
                    if (in.a == NO_TEMP || in.a == in.dst || self.rel(in.a) < 0) { continue; }
                    f = self.addFact(F_REL, IROp.CmpLe, in.dst, in.a, 0, false, uns, -1);
                } else {
                    l: long = self.instLoc.get(i);
                    if (l < 0 || self.lRootKind.get(l) == R_GLOBAL || self.instFact.get(i) < 0) { continue; }
                    f = self.addFact(F_LREL, IROp.CmpLe, in.dst, NO_TEMP, 0, false, uns, l);
                }
                self.jcList.push(f);
            }
            self.jcCount.set(b, self.jcList.len() - self.jcFirst.get(b));
        }
    }

    // Add to the set at `at` (block `b`'s meet) every candidate a predecessor's write makes true
    // on every edge in.
    deriveJoin &self inout p:IRProgram b:long at:long -> void {
        pf: long = self.predFirst.get(b);
        np: long = self.predCount.get(b);
        if (np < 2) { return; }
        for k in 0..np {
            pb: long = self.predBlock.get(pf + k);
            if (!self.reach.get(pb)) { continue; }
            for z in 0..self.jcCount.get(pb) {
                f: long = self.jcList.get(self.jcFirst.get(pb) + z);
                if (self.has(at, f)) { continue; }
                ok: bool = true;
                e: long = 0;
                while (ok && e < np) {
                    qb: long = self.predBlock.get(pf + e);
                    if (self.reach.get(qb) && !self.holdsOnEdge(p, f, qb, self.predKind.get(pf + e))) { ok = false; }
                    e = e + 1;
                }
                if (ok) { self.touch(at, f, 1); }
            }
        }
    }

    // Whether candidate `f` (`t <= [loc]` or `t <= u`) holds at the end of the edge from `pb`.
    holdsOnEdge &self inout p:IRProgram f:long pb:long kind:long -> bool {
        if (self.has(self.setAt(pb, SET_OUT), f)) { return true; }
        c: long = self.bCond.get(pb);
        if (kind == E_FALL) { c = self.bNeg.get(pb); }
        if (self.bTaken.get(pb) == self.bFall.get(pb)) { c = -1; }
        if (c == f) { return true; }
        if (self.fIsImm.get(f)) { return self.immHolds(p, f, pb, c); }
        t: Temp = self.fA.get(f);
        lrel: bool = self.fKind.get(f) == F_LREL;
        uns: bool = self.fUns.get(f);
        // The block's last write of t, and what comes after it: a write of memory, a write of
        // the other temp.
        d: long = -1;
        memAfter: bool = false;
        otherAfter: bool = false;
        i: long = self.stopOf(pb) - 1;
        while (i >= self.bStart.get(pb) && d < 0) {
            ix: long = self.first + i;
            o: IROp = p.code[ix].op;
            if (o != IROp.Nop && p.code[ix].dst == t) { d = i; continue; }
            if (o == IROp.PtrStore || o == IROp.Store || o == IROp.AggCopy || o == IROp.AggZero || o == IROp.ArrStore
                || o == IROp.Call || o == IROp.CallIndirect || o == IROp.Asm || o == IROp.Atomic || o == IROp.MemCopy) { memAfter = true; }
            if (!lrel && o != IROp.Nop && p.code[ix].dst == self.fB.get(f)) { otherAfter = true; }
            i = i - 1;
        }
        W: long = self.words;
        at: long = (self.bStart.len() * 4 + 1) * W;
        // As the edge leaves: its block's facts and the branch's on this edge, asked of t, and of
        // the temp t was last copied from when neither has been written since.
        out: long = self.setAt(pb, SET_OUT);
        for w in 0..W { self.bits.set(at + w, self.bits.get(out + w)); }
        if (c >= 0) { self.touch(at, c, 1); }
        self.jcVals.clear();
        self.jcVals.push(t);
        if (d >= 0 && p.code[self.first + d].op == IROp.Mov && p.code[self.first + d].a != NO_TEMP
            && !self.writtenAfter(p, pb, d, p.code[self.first + d].a)) {
            self.jcVals.push(p.code[self.first + d].a);
        }
        self.jcWs.clear();
        if (lrel) { self.memTemps(self.fLoc.get(f), at, false); }
        else { self.jcWs.push(self.fB.get(f)); }
        if (self.anyLe(p, uns, at)) { return true; }
        // Just before the write, with t's new value: valid at the end when nothing after it
        // writes memory or the other temp.
        if (d < 0 || memAfter || otherAfter) { return false; }
        dix: long = self.first + d;
        od: IROp = p.code[dix].op;
        if (od != IROp.Mov && od != IROp.PtrLoad && od != IROp.Load) { return false; }
        in0: long = self.setAt(pb, SET_IN);
        for w in 0..W { self.bits.set(at + w, self.bits.get(in0 + w)); }
        for j in self.bStart.get(pb)..d { self.step(p, j, at); }
        // What t is given: the copy's source, or any temp holding the location loaded.
        self.jcVals.clear();
        if (od == IROp.Mov) {
            if (p.code[dix].a == NO_TEMP) { return false; }
            self.jcVals.push(p.code[dix].a);
        } else {
            dl: long = self.instLoc.get(d);
            if (dl < 0) { return false; }
            // Loading the very location of the candidate: t is what it holds.
            if (lrel && dl == self.fLoc.get(f)) { return true; }
            self.memTemps(dl, at, true);
        }
        // What t is held against: the other temp, or any temp holding the location.
        self.jcWs.clear();
        if (lrel) { self.memTemps(self.fLoc.get(f), at, false); }
        else { self.jcWs.push(self.fB.get(f)); }
        return self.anyLe(p, uns, at);
    }

    // Whether candidate `f`, `t op c` against a constant, holds at the end of the edge from `pb`,
    // whose branch establishes `cond` (or -1). The bound a loop counter starts from is the shape
    // this is for: `i = from; if (i < 0) { i = 0; }` leaves `i >= 0` after the join, and the
    // counter copied from `i` and stepped by one keeps it round the loop, so the bounds check of
    // `hay[i]` under `i < hay.len` goes. Asked two ways, as `holdsOnEdge` asks a relation:
    //   * as the edge leaves, of t, or of the temp t was last copied from when that is unwritten
    //     since (the edge's own branch included: `jcc if from >= 0` after `i = from`);
    //   * by the block's last write of t, which a constant answers by its value, a copy by what
    //     the facts say of its source just before, and `t = t + 1` by `t op c` just before (for
    //     `>=` and `>` signed, which adding one keeps) together with a fact putting t strictly
    //     below something there, so that adding one does not wrap at t's width.
    // Each is true where control leaves the block: nothing after the write changes t or c.
    immHolds &self inout p:IRProgram f:long pb:long cond:long -> bool {
        t: Temp = self.fA.get(f);
        op: IROp = self.fOp.get(f);
        c: long = self.fImm.get(f);
        uns: bool = self.fUns.get(f);
        d: long = -1;
        i: long = self.stopOf(pb) - 1;
        while (i >= self.bStart.get(pb) && d < 0) {
            ix: long = self.first + i;
            if (p.code[ix].op != IROp.Nop && p.code[ix].dst == t) { d = i; }
            i = i - 1;
        }
        W: long = self.words;
        at: long = (self.bStart.len() * 4 + 1) * W;
        out: long = self.setAt(pb, SET_OUT);
        for w in 0..W { self.bits.set(at + w, self.bits.get(out + w)); }
        if (cond >= 0) { self.touch(at, cond, 1); }
        if (self.decide(p, op, t, NO_TEMP, true, c, uns, at) == 1) { return true; }
        if (d < 0) { return false; }
        dix: long = self.first + d;
        od: IROp = p.code[dix].op;
        src: Temp = p.code[dix].a;
        if (od == IROp.Mov && src != NO_TEMP && !self.writtenAfter(p, pb, d, src)
            && self.decide(p, op, src, NO_TEMP, true, c, uns, at) == 1) { return true; }
        if (od == IROp.Const) { return compareHolds(op, p.code[dix].imm, c, uns); }
        // Just before the write.
        in0: long = self.setAt(pb, SET_IN);
        for w in 0..W { self.bits.set(at + w, self.bits.get(in0 + w)); }
        for j in self.bStart.get(pb)..d { self.step(p, j, at); }
        if (od == IROp.Mov) { return src != NO_TEMP && self.decide(p, op, src, NO_TEMP, true, c, uns, at) == 1; }
        if (od == IROp.Add && src == t && p.code[dix].bIsImm && p.code[dix].bImm == 1 && !uns
            && (op == IROp.CmpGe || op == IROp.CmpGt)) {
            // The candidate itself before the step is the induction: asked as a fact rather than
            // through `decide`, whose interval is empty (and so undecided) wherever the optimistic
            // start still holds every fact, `t < 0` beside `t >= 0`.
            return (self.has(at, f) || self.decide(p, op, t, NO_TEMP, true, c, false, at) == 1) && self.strictlyBelow(t, at);
        }
        return false;
    }

    // Whether the facts at `at` put `t` strictly below something, as signed values: `t < u`,
    // `u > t` or `t < c`. Then `t + 1` does not pass the largest value t's type holds.
    strictlyBelow &self t:Temp at:long -> bool {
        r: long = self.rel(t);
        if (r < 0) { return false; }
        s: long = self.tfFirst.get(r);
        for k in 0..self.tfCount.get(r) {
            g: long = self.tfList.get(s + k);
            if (self.fKind.get(g) != F_REL || self.fUns.get(g) || !self.has(at, g)) { continue; }
            o: IROp = self.fOp.get(g);
            if ((self.fA.get(g) == t && o == IROp.CmpLt) || (!self.fIsImm.get(g) && self.fB.get(g) == t && o == IROp.CmpGt)) {
                return true;
            }
        }
        return false;
    }

    // Whether some value in `jcVals` is at most some value in `jcWs` by the facts at `at`.
    anyLe &self inout p:IRProgram uns:bool at:long -> bool {
        for a in 0..self.jcVals.len() {
            v: Temp = self.jcVals.get(a);
            for b in 0..self.jcWs.len() {
                w: Temp = self.jcWs.get(b);
                if (v == w) { return true; }
                if (self.decide(p, IROp.CmpLe, v, w, false, 0, uns, at) == 1) { return true; }
            }
        }
        return false;
    }

    // Whether instruction `d` of block `b` is followed in the block by a write of `t`.
    writtenAfter &self inout p:IRProgram b:long d:long t:Temp -> bool {
        for j in d + 1..self.stopOf(b) {
            ix: long = self.first + j;
            if (p.code[ix].op != IROp.Nop && p.code[ix].dst == t) { return true; }
        }
        return false;
    }

    // Every temp the facts at `at` say location `l` holds, onto `jcVals` or `jcWs`.
    memTemps &self l:long at:long toVals:bool -> void {
        g: long = self.locFactHead.get(l);
        while (g >= 0) {
            if (self.fKind.get(g) == F_MEM && self.has(at, g)) { if (toVals) { self.jcVals.push(self.fA.get(g)); } else { self.jcWs.push(self.fA.get(g)); } }
            g = self.factNext.get(g);
        }
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
        self.killMem(p, i, at, mode);
    }

    // What instruction `i` ends by writing memory (a store, a call, `asm`, a block copy or fill).
    killMem &self inout p:IRProgram i:long at:long mode:long -> void {
        ix: long = self.first + i;
        o: IROp = p.code[ix].op;
        if (o == IROp.Call) { self.killCall(p, i, at, mode); return; }
        if (o == IROp.CallIndirect) { self.killUnknownCall(p, i, at, mode); return; }
        if (o == IROp.Asm) { self.touchSet(at, 1, mode); return; }
        // What another thread may have written shows from an atomic on: everything a call can
        // reach ends, as at a call that writes it all. A frame slot nothing else can reach stays.
        if (o == IROp.Atomic) { self.touchSet(at, 0, mode); return; }
        // A `memcpy` writes its destination range and nothing else: from `a` on, its length being
        // a value the program computes. A borrowed parameter's own bytes stay known unless `a`
        // may point into them (`killRegion`), which is what keeps a `String`'s fields across the
        // copy into its buffer.
        if (o == IROp.MemCopy) { self.killThrough(at, mode, p.code[ix].a, 0, LONG_MAX / 4); return; }
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

    // What a call ends. Without its callee's summary, or when the callee is wild, that is
    // everything a call can reach (`callKill`): memory through pointers, exposed slots and
    // globals, but not a lent slot. With a summary, it adds what the callee writes through each
    // argument, as a store of that many bytes there would.
    killCall &self inout p:IRProgram i:long at:long mode:long -> void {
        s: long = self.callFx.get(i);
        if (s < 0) { self.killUnknownCall(p, i, at, mode); return; }
        if (fxWild(s)) { self.touchSet(at, 3, mode); }
        ix: long = self.first + i;
        fa: long = p.code[ix].firstArg;
        for k in 0..p.code[ix].argCount {
            if (!fxWrites(s, k)) { continue; }
            t: Temp = p.args.get(fa + k);
            // A wild callee's write through a pointer of no known origin ends nothing the line
            // above did not end already.
            if (fxWild(s) && self.acOf(t) < 0 && self.bpOf(t) == 0) { continue; }
            if (fxAllOver(s, k)) { self.killThrough(at, mode, t, LONG_MIN / 4, LONG_MAX / 2); continue; }
            for j in 0..fxRangeCount(s, k) { self.killThrough(at, mode, t, fxRangeOff(s, k, j), fxRangeW(s, k, j)); }
        }
    }

    // A call whose callee's summary is not known (a call through a pointer, a recursive one, another
    // package's without one): everything a call can reach but a borrowed parameter's own bytes and a
    // lent slot, and then what it may write through each argument, by its callee's conventions
    // (`callMayWrite`; all of them when those are not known).
    killUnknownCall &self inout p:IRProgram i:long at:long mode:long -> void {
        self.touchSet(at, 3, mode);
        ix: long = self.first + i;
        fa: long = p.code[ix].firstArg;
        cc: long = p.code[ix].imm;
        if (gLentOff) { cc = 0; }
        for k in 0..p.code[ix].argCount {
            if (!callMayWrite(cc, k)) { continue; }
            // What a pointer of no known origin reaches, the first line ended already: only a slot
            // lent here and a borrowed parameter's own bytes are left to end.
            t: Temp = p.args.get(fa + k);
            if (self.acOf(t) >= 0) { self.killThrough(at, mode, t, LONG_MIN / 4, LONG_MAX / 2); }
            else if (self.bpOf(t) != 0) { self.touchOwnOf(at, t, mode); }
        }
    }

    // A write of `w` bytes at `[t + off]`, `t` an address constant or any pointer.
    killThrough &self at:long mode:long t:Temp off:long w:long -> void {
        r: long = self.rel(t);
        if (r >= 0 && self.acRoot.get(r) >= 0) {
            self.killRegion(at, mode, self.acKind.get(r), self.acRoot.get(r), self.acOff.get(r) + off, w);
        } else {
            self.killRegion(at, mode, R_TEMP, t, off, w);
        }
    }

    touch &self at:long f:long mode:long -> void {
        w: long = at + f / 64;
        m: long = 1 << (f % 64);
        if (mode == 0) { self.bits.set(w, self.bits.get(w) & ~m); }
        else { self.bits.set(w, self.bits.get(w) | m); }
    }

    // The same for a whole set: what a call ends (0), what `asm` ends (1), what a pointer reaches (2),
    // and the first and the last without the facts about borrowed parameters' own bytes (3, 4).
    touchSet &self at:long which:long mode:long -> void {
        k: long = which;
        if (k >= 3 && self.bpParam.len() == 0) { k = (k - 3) * 2; }
        for w in 0..self.words {
            s: long = 0;
            if (k == 0) { s = self.callKill.get(w); }
            else if (k == 1) { s = self.allMem.get(w); }
            else if (k == 2) { s = self.tempMem.get(w); }
            else if (k == 3) { s = self.callOther.get(w); }
            else { s = self.tempOther.get(w); }
            if (mode == 0) { self.bits.set(at + w, self.bits.get(at + w) & ~s); }
            else { self.bits.set(at + w, self.bits.get(at + w) | s); }
        }
    }

    // The facts about borrowed parameter `j`'s own bytes (`ownSets`), cleared or added as `touchSet`.
    touchOwn &self at:long j:long mode:long -> void {
        b: long = j * self.words;
        for w in 0..self.words {
            s: long = self.ownSets.get(b + w);
            if (s == 0) { continue; }
            if (mode == 0) { self.bits.set(at + w, self.bits.get(at + w) & ~s); }
            else { self.bits.set(at + w, self.bits.get(at + w) | s); }
        }
    }
    // What a write through temp `t`, or a call handed it, may reach besides what any write
    // through a pointer reaches: the own bytes of each borrowed parameter `t` may be derived from.
    touchOwnOf &self at:long t:Temp mode:long -> void {
        m: long = self.bpOf(t);
        j: long = 0;
        while (m != 0) {
            if ((m & 1) != 0) { self.touchOwn(at, j, mode); }
            m = m >> 1;
            j = j + 1;
        }
    }

    has &self at:long f:long -> bool {
        return (self.bits.get(at + f / 64) & (1 << (f % 64))) != 0;
    }

    solve &self inout p:IRProgram -> void {
        nb: long = self.bStart.len();
        W: long = self.words;
        fillLong(&self.bits, (nb * 4 + 2) * W, 0);
        scratch: long = nb * 4 * W;     // one more set, for the meet, and one past it (`deriveJoin`)
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
                if (self.jcList.len() > 0) { self.deriveJoin(p, b, scratch); }
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
            k: long = self.copyAt.get(i);
            if (k >= 0) { c = self.cmCount.get(k); s = self.cmFirst.get(k); }
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
        if (self.rOn && self.rLo.get(r) <= self.rHi.get(r)) { self.lo = self.rLo.get(r); self.hi = self.rHi.get(r); }
        if (self.nonneg.len() > r && self.nonneg.get(r) && self.lo < 0) { self.lo = 0; }
        s: long = self.tfFirst.get(r);
        for k in 0..self.tfCount.get(r) {
            f: long = self.tfList.get(s + k);
            if (self.fKind.get(f) != F_REL || !self.fIsImm.get(f) || self.fA.get(f) != t) { continue; }
            if (!self.has(at, f)) { continue; }
            c: long = self.fImm.get(f);
            o: IROp = self.fOp.get(f);
            if (self.fUns.get(f)) {
                // Unsigned `t < c` with c >= 0 puts t's bits below c: t is in [0, c - 1] as a
                // signed value too. (`>` says nothing a signed interval can hold.)
                if ((o == IROp.CmpLt && c > 0) || (o == IROp.CmpLe && c >= 0)) {
                    if (self.lo < 0) { self.lo = 0; }
                    top: long = c;
                    if (o == IROp.CmpLt) { top = c - 1; }
                    if (top < self.hi) { self.hi = top; }
                } else if (o == IROp.CmpEq) { if (c > self.lo) { self.lo = c; } if (c < self.hi) { self.hi = c; } }
                continue;
            }
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
        d: long = self.decideOne(p, op, a, b, isImm, imm, uns, at);
        if (d >= 0 || self.transDepth != 0) { return d; }
        // Two temps loaded from one location hold one value there: what the facts say of the
        // other is said of this one (a length read twice, the check against the second read).
        self.transDepth = 1;
        d = self.decideSameLoc(p, op, a, b, isImm, imm, uns, at, true);
        if (d < 0 && !isImm && b != NO_TEMP) { d = self.decideSameLoc(p, op, a, b, isImm, imm, uns, at, false); }
        self.transDepth = 0;
        return d;
    }

    // `decide` with `a` (or `b`) replaced by each other temp a location holding it holds too.
    decideSameLoc &self inout p:IRProgram op:IROp a:Temp b:Temp isImm:bool imm:long uns:bool at:long left:bool -> long {
        t: Temp = b;
        if (left) { t = a; }
        r: long = self.rel(t);
        if (r < 0) { return -1; }
        s: long = self.tfFirst.get(r);
        for k in 0..self.tfCount.get(r) {
            f: long = self.tfList.get(s + k);
            if (self.fKind.get(f) != F_MEM || self.fA.get(f) != t || !self.has(at, f)) { continue; }
            g: long = self.locFactHead.get(self.fLoc.get(f));
            while (g >= 0) {
                u: Temp = self.fA.get(g);
                if (self.fKind.get(g) == F_MEM && u != t && self.has(at, g)) {
                    d: long = -1;
                    if (left) { d = self.decideOne(p, op, u, b, isImm, imm, uns, at); }
                    else { d = self.decideOne(p, op, a, u, isImm, imm, uns, at); }
                    if (d >= 0) { return d; }
                }
                g = self.factNext.get(g);
            }
        }
        return -1;
    }

    decideOne &self inout p:IRProgram op:IROp a:Temp b:Temp isImm:bool imm:long uns:bool at:long -> long {
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
                // `a op [loc]`, where `b` holds what `loc` does here.
                if (self.fKind.get(f) == F_LREL && self.fA.get(f) == a && self.has(at, f) && self.memHolds(self.fLoc.get(f), b, at)) {
                    lop: IROp = self.fOp.get(f);
                    if (self.signsAgree(p, lop, self.fUns.get(f), uns, a, b, at)) {
                        if (implies(lop, op)) { return 1; }
                        if (implies(lop, negateCompare(op))) { return 0; }
                    }
                    continue;
                }
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
        // Two intervals that do not overlap, or meet only at the edge. Unsigned, only where both
        // are never negative: there the two orders agree.
        self.interval(p, a, at);
        alo: long = self.lo;
        ahi: long = self.hi;
        self.interval(p, b, at);
        if (uns && (alo < 0 || self.lo < 0)) { return -1; }
        return orderIntervals(op, alo, ahi, self.lo, self.hi);
    }

    // `a op b` (an order) through a third value c: a fact `a < c` or `a <= c`, and then `c <= b`
    // or `c < b` as far as everything else known says (the facts and the intervals, but not a
    // third step). `i < mid` with `mid <= len` gives `i < len`. The chain is read in the fact's
    // signedness. A question asked unsigned is answered by a signed chain only when `a` is never
    // negative: then b, above it, is not negative either, and the two orders agree. This only
    // ever says "holds" (1) or nothing (-1).
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

    // ─── value ranges ────────────────────────────────────────────────────────

    // Before `boundWalk`: every temp starts with no value, except a temp with no definition here,
    // or with one `evalRange` can only answer "anything" for (a load by name, a call, an address,
    // a float). Those are the whole line, for good. The definitions left to evaluate are listed
    // in reverse postorder (`rDefs`).
    rangeSetup &self inout p:IRProgram -> void {
        fillLong(&self.rLo, self.nt, LONG_MAX);
        fillLong(&self.rHi, self.nt, LONG_MIN);
        fillBool(&self.rFixed, self.nt, false);
        for r in 0..self.nt {
            if (self.defs.get(r) == 0) { self.rLo.set(r, LONG_MIN); self.rHi.set(r, LONG_MAX); self.rFixed.set(r, true); }
        }
        self.rDefs.clear();
        for oi in 0..self.order.len() {
            b: long = self.order.get(oi);
            for i in self.bStart.get(b)..self.stopOf(b) {
                ix: long = self.first + i;
                r: long = self.rel(p.code[ix].dst);
                if (r < 0) { continue; }
                if (self.rangeEvaluable(p, ix)) { self.rDefs.push(i); }
                else { self.rLo.set(r, LONG_MIN); self.rHi.set(r, LONG_MAX); self.rFixed.set(r, true); }
            }
        }
    }

    // Whether `evalRange` can say more than "anything" of what instruction `ix` gives.
    rangeEvaluable &self inout p:IRProgram ix:long -> bool {
        o: IROp = p.code[ix].op;
        if (o == IROp.Const || isCompare(o)) { return true; }
        k: Lit = p.code[ix].kind;
        if (isFloatKind(k)) { return false; }
        if (o == IROp.PtrLoad) { return !isAggregate(k) && kindWidth(k) < 8; }
        if (o == IROp.Convert) { return !isFloatKind(p.code[ix].fromKind) && !isFloatKind(p.code[ix].toKind); }
        return self.rangedOp(o);
    }

    // The signed interval each temp's value lies in, wherever it holds one: the hull of what each
    // of its definitions can produce. Each definition is evaluated with its operands' ranges
    // narrowed by the facts that hold where it stands, so `i + 1` under `i < 8` is at most 8, and
    // under `i < n` at most n's largest value. A value written on two paths
    // (`k = 2; if (b) { k = 5; }`) is in [2, 5] after the join, `x & 7` is in [0, 7], an unsigned
    // `x % 8` is in [0, 7], and a conversion keeps the range when both types hold it. Every
    // operation is evaluated as the emitter computes it, at its width and signedness
    // (`evalRange`), and a result that might wrap gets its type's whole range.
    //
    // The iteration ascends from "no value yet", taking the hull at every definition. From the
    // fourth round on, a bound that still moves jumps to the end of the line (widening), so a
    // loop's fixpoint comes in a few rounds. Where it widened, two more rounds recompute every
    // range from the others (narrowing, which starts from a post-fixpoint, only tightens, and
    // stays a post-fixpoint), and a last round checks that it still is one, dropping the ranges
    // if not. Without widening, the last ascending round, which changed nothing, already was that
    // check. This is sound for the same reason `computeNonneg` is: every temp read was written
    // first, so by induction over a run, every value a definition writes lies in its temp's range.
    computeRanges &self inout p:IRProgram -> void {
        self.rOn = false;
        rounds: long = 0;
        going: bool = true;
        widened: bool = false;
        while (going && rounds < 16) {
            going = false;
            widen: bool = rounds >= 3;
            if (widen) { widened = true; }
            for d in 0..self.rDefs.len() {
                i: long = self.rDefs.get(d);
                r: long = self.rel(p.code[self.first + i].dst);
                ol: long = self.rLo.get(r);
                oh: long = self.rHi.get(r);
                if (ol == LONG_MIN && oh == LONG_MAX) { continue; }      // nothing can widen it
                in: Instr = p.code.get(self.first + i);
                if (!self.evalRange(p, in, i)) { continue; }
                if (ol > oh) { self.rLo.set(r, self.lo); self.rHi.set(r, self.hi); going = true; continue; }
                if (self.lo < ol) { if (widen) { self.rLo.set(r, LONG_MIN); } else { self.rLo.set(r, self.lo); } going = true; }
                if (self.hi > oh) { if (widen) { self.rHi.set(r, LONG_MAX); } else { self.rHi.set(r, self.hi); } going = true; }
            }
            rounds = rounds + 1;
        }
        if (going) { return; }
        self.rOn = true;
        // A round that changed nothing evaluated every definition against the final ranges, so
        // without widening they are already the least fixpoint, and checked.
        if (!widened) { return; }
        for k in 0..2 { self.rangeRound(p, true); }
        if (!self.rangeRound(p, false)) { self.rOn = false; }
    }

    // One round over every definition with the ranges as they stand: narrowing each to the hull
    // of what its definitions now give (`narrow`), or checking that every definition's value lies
    // in its temp's range. False when the check fails.
    rangeRound &self inout p:IRProgram narrow:bool -> bool {
        if (narrow) {
            fillLong(&self.nLo, self.nt, LONG_MAX);
            fillLong(&self.nHi, self.nt, LONG_MIN);
        }
        for d in 0..self.rDefs.len() {
            i: long = self.rDefs.get(d);
            r: long = self.rel(p.code[self.first + i].dst);
            // A temp some definition outside the list makes the whole line is never narrowed from
            // the others; checking the whole line is a waste.
            if (self.rFixed.get(r) || (!narrow && self.rLo.get(r) == LONG_MIN && self.rHi.get(r) == LONG_MAX)) { continue; }
            in: Instr = p.code.get(self.first + i);
            if (!self.evalRange(p, in, i)) { continue; }
            if (!narrow) {
                if (self.rLo.get(r) > self.rHi.get(r) || self.lo < self.rLo.get(r) || self.hi > self.rHi.get(r)) { return false; }
                continue;
            }
            if (self.lo < self.nLo.get(r)) { self.nLo.set(r, self.lo); }
            if (self.hi > self.nHi.get(r)) { self.nHi.set(r, self.hi); }
        }
        if (!narrow) { return true; }
        for r in 0..self.nt {
            if (self.rFixed.get(r) || self.nLo.get(r) > self.nHi.get(r) || self.rLo.get(r) > self.rHi.get(r)) { continue; }
            if (self.nLo.get(r) > self.rLo.get(r)) { self.rLo.set(r, self.nLo.get(r)); }
            if (self.nHi.get(r) < self.rHi.get(r)) { self.rHi.set(r, self.nHi.get(r)); }
        }
        return true;
    }

    // The operations `evalRange` reads its operands' ranges for.
    rangedOp &self o:IROp -> bool {
        return isArith(o) || o == IROp.Mov || o == IROp.Convert || o == IROp.BNot;
    }

    // What the facts at `at` say of instruction `i`'s operands, kept for `evalRange`: an
    // interval for each, and a temp the first is (signed) below.
    noteOperands &self inout p:IRProgram in:Instr i:long at:long -> void {
        if (in.a != NO_TEMP) {
            self.interval(p, in.a, at);
            self.oaLo.set(i, self.lo);
            self.oaHi.set(i, self.hi);
            self.oaUp.set(i, self.upperTemp(in.a, at));
        }
        if (!in.bIsImm && in.b != NO_TEMP) {
            self.interval(p, in.b, at);
            self.obLo.set(i, self.lo);
            self.obHi.set(i, self.hi);
        }
    }

    // A fact `x < y` or `x <= y` (signed, between temps) holding at `at`: `(y << 1) | strict`, or -1.
    upperTemp &self x:Temp at:long -> long {
        r: long = self.rel(x);
        if (r < 0) { return -1; }
        s: long = self.tfFirst.get(r);
        for j in 0..self.tfCount.get(r) {
            f: long = self.tfList.get(s + j);
            if (self.fKind.get(f) != F_REL || self.fIsImm.get(f) || self.fUns.get(f) || !self.has(at, f)) { continue; }
            o: IROp = self.fOp.get(f);
            y: Temp = NO_TEMP;
            if (self.fA.get(f) == x && (o == IROp.CmpLt || o == IROp.CmpLe)) { y = self.fB.get(f); }
            else if (self.fB.get(f) == x && (o == IROp.CmpGt || o == IROp.CmpGe)) { y = self.fA.get(f); o = swapCompare(o); }
            if (y == NO_TEMP || y == x || self.rel(y) < 0) { continue; }
            if (o == IROp.CmpLt) { return (y << 1) | 1; }
            return y << 1;
        }
        return -1;
    }

    // Operand `t` of instruction `i` (`side` 0: its `a`, 1: its `b`): its range there, narrowed
    // by what the facts said (`noteOperands`), in `lo`/`hi`. False when it has no value yet.
    operandRange &self inout p:IRProgram t:Temp i:long side:long -> bool {
        if (t == NO_TEMP) { self.lo = LONG_MIN; self.hi = LONG_MAX; return true; }
        if (self.singleConst(p, t)) { self.lo = self.cv; self.hi = self.cv; return true; }
        lo: long = LONG_MIN;
        hi: long = LONG_MAX;
        r: long = self.rel(t);
        if (r >= 0) {
            lo = self.rLo.get(r);
            hi = self.rHi.get(r);
            if (lo > hi) { return false; }
        }
        fl: long = self.oaLo.get(i);
        fh: long = self.oaHi.get(i);
        if (side == 1) { fl = self.obLo.get(i); fh = self.obHi.get(i); }
        if (fl > lo) { lo = fl; }
        if (fh < hi) { hi = fh; }
        if (side == 0 && self.oaUp.get(i) >= 0) {
            u: long = self.oaUp.get(i);
            ur: long = self.rel(u >> 1);
            if (ur >= 0 && self.rLo.get(ur) <= self.rHi.get(ur)) {
                uh: long = self.rHi.get(ur);
                if ((u & 1) == 1 && uh > LONG_MIN) { uh = uh - 1; }
                if (uh < hi) { hi = uh; }
            }
        }
        // The facts there contradict every value it can hold: no run reaches this with one.
        if (lo > hi) { return false; }
        self.lo = lo;
        self.hi = hi;
        return true;
    }

    // The interval instruction `in` (at `i`) gives its destination, in `lo`/`hi`, with its
    // operands' ranges as they stand; false when an operand has no value yet.
    evalRange &self inout p:IRProgram in:Instr i:long -> bool {
        o: IROp = in.op;
        k: Lit = in.kind;
        if (o == IROp.Const) { self.lo = in.imm; self.hi = in.imm; return true; }
        if (isCompare(o)) { self.lo = 0; self.hi = 1; return true; }
        if (o == IROp.PtrLoad && !isFloatKind(k) && !isAggregate(k)) {
            // A sized load extends what it reads, by the type's signedness.
            self.lo = kindLo(k);
            self.hi = kindMax(k);
            return true;
        }
        self.lo = LONG_MIN;
        self.hi = LONG_MAX;
        if (!self.rangedOp(o) || isFloatKind(k)) { return true; }
        if (o == IROp.Convert && (isFloatKind(in.fromKind) || isFloatKind(in.toKind))) { return true; }
        if (!self.operandRange(p, in.a, i, 0)) { return false; }
        alo: long = self.lo;
        ahi: long = self.hi;
        if (o == IROp.Mov) { return true; }
        if (o == IROp.Convert) {
            // Unchanged where both types hold every value it can have; else the target's range.
            f: Lit = in.fromKind;
            t: Lit = in.toKind;
            if (!(alo >= kindLo(f) && ahi <= kindMax(f) && alo >= kindLo(t) && ahi <= kindMax(t))) {
                self.lo = kindLo(t);
                self.hi = kindMax(t);
            }
            return true;
        }
        if (o == IROp.BNot) { self.lo = ~ahi; self.hi = ~alo; self.fitKind(k); return true; }
        blo: long = 0;
        bhi: long = 0;
        if (in.bIsImm) { blo = in.bImm; bhi = in.bImm; }
        else {
            if (!self.operandRange(p, in.b, i, 1)) { return false; }
            blo = self.lo;
            bhi = self.hi;
        }
        self.lo = LONG_MIN;
        self.hi = LONG_MAX;
        uns: bool = kindUnsigned(k);
        if (o == IROp.Add) {
            if (!addWraps(alo, blo) && !addWraps(ahi, bhi)) { self.lo = alo + blo; self.hi = ahi + bhi; }
        } else if (o == IROp.Sub) {
            if (!subWraps(alo, bhi) && !subWraps(ahi, blo)) { self.lo = alo - bhi; self.hi = ahi - blo; }
        } else if (o == IROp.Mul) {
            if (!mulWraps(alo, blo) && !mulWraps(alo, bhi) && !mulWraps(ahi, blo) && !mulWraps(ahi, bhi)) {
                self.lo = min4(alo * blo, alo * bhi, ahi * blo, ahi * bhi);
                self.hi = max4(alo * blo, alo * bhi, ahi * blo, ahi * bhi);
            }
        } else if (o == IROp.Shl) {
            if (in.bIsImm) {
                c: long = in.bImm & 63;
                if (alo >= (LONG_MIN >> c) && ahi <= (LONG_MAX >> c)) { self.lo = alo << c; self.hi = ahi << c; }
            }
        } else if (o == IROp.Shr) {
            if (in.bIsImm) {
                c: long = in.bImm & 63;
                if (!uns || alo >= 0) { self.lo = alo >> c; self.hi = ahi >> c; }
                else if (kindWidth(k) == 8) {
                    // A logical shift of a word with its top bit set.
                    if (c == 0) { self.lo = alo; self.hi = ahi; } else { self.lo = 0; self.hi = LONG_MAX >> (c - 1); }
                }
            }
        } else if (o == IROp.BAnd) {
            // Never negative where either side is not, and at most that side.
            if (alo >= 0 && blo >= 0) { self.lo = 0; self.hi = ahi; if (bhi < ahi) { self.hi = bhi; } }
            else if (alo >= 0) { self.lo = 0; self.hi = ahi; }
            else if (blo >= 0) { self.lo = 0; self.hi = bhi; }
        } else if (o == IROp.BOr || o == IROp.BXor) {
            if (alo >= 0 && blo >= 0) {
                self.lo = 0;
                if (o == IROp.BOr) { self.lo = alo; if (blo > alo) { self.lo = blo; } }
                m: long = ahi;
                if (bhi > m) { m = bhi; }
                self.hi = onesAbove(m);
            }
        } else if (o == IROp.Div) {
            if (blo == bhi && blo > 0) {
                if (!uns || alo >= 0) { self.lo = alo / blo; self.hi = ahi / blo; }
                else if (blo > 1 && kindWidth(k) == 8) { self.lo = 0; self.hi = ((-1 as u64) / (blo as u64)) as long; }
            } else if (blo >= 1 && alo >= 0) { self.lo = 0; self.hi = ahi / blo; }
        } else if (o == IROp.Mod) {
            // The remainder is below the divisor, and has the dividend's sign (signed) or none.
            if (blo >= 1) {
                d: long = bhi - 1;
                if (alo >= 0) { self.lo = 0; self.hi = d; if (ahi < d) { self.hi = ahi; } }
                else if (uns) { self.lo = 0; self.hi = d; }
                else if (ahi <= 0) { self.lo = 0 - d; if (alo > self.lo) { self.lo = alo; } self.hi = 0; }
                else { self.lo = 0 - d; self.hi = d; }
            }
        }
        self.fitKind(k);
        return true;
    }

    // `lo`/`hi` as a value of type `k` holds them: unchanged when they fit its canonical range,
    // else all of that range (the operation wrapped).
    fitKind &self k:Lit -> void {
        if (self.lo >= kindLo(k) && self.hi <= kindMax(k) && self.lo <= self.hi) { return; }
        self.lo = kindLo(k);
        self.hi = kindMax(k);
    }

    // ─── values that are never negative ──────────────────────────────────────

    // Before `computeNonneg`: for each `x + y`, `x << k` and `x * y`, whether the result cannot
    // wrap past the largest value of its type when its operands are never negative (`addOk`), so
    // that `yieldsNonneg` may call the result never negative when the operands are. The bound on
    // an operand is what the facts at that point say or, for a temp with one definition, the
    // bound that definition was found to have (`condHi`), which assumes the same thing: that its
    // own operands are never negative. That is exactly what `computeNonneg` then checks of every
    // operand along the way (a temp stays never negative only while each of its definitions'
    // operands is), so the bounds hold wherever the conclusion is drawn. This is what puts
    // `lo + width` (two values that are each below a bound) and `width * 2` among the values
    // never negative: the merge sort's indexes.
    boundWalk &self inout p:IRProgram -> void {
        self.addOk.clear();
        for i in 0..self.n { self.addOk.push(false); }
        fillLong(&self.condHi, self.nt, LONG_MAX);
        fillLong(&self.oaLo, self.n, LONG_MIN);
        fillLong(&self.oaHi, self.n, LONG_MAX);
        fillLong(&self.obLo, self.n, LONG_MIN);
        fillLong(&self.obHi, self.n, LONG_MAX);
        fillLong(&self.oaUp, self.n, -1);
        self.nonneg.clear();
        for oi in 0..self.order.len() {
            b: long = self.order.get(oi);
            at: long = self.startWalk(b);
            for i in self.bStart.get(b)..self.stopOf(b) {
                in: Instr = p.code.get(self.first + i);
                o: IROp = in.op;
                rd: long = self.rel(in.dst);
                if (rd >= 0 && self.rLo.get(rd) != LONG_MIN && self.rangedOp(o) && !isFloatKind(in.kind)) { self.noteOperands(p, in, i, at); }
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
                else if (!gXorBoundsOff && in.a != NO_TEMP && (o == IROp.BXor || o == IROp.BOr)) {
                    // Of two values never negative, each below 2^k: below 2^k too.
                    ua: long = self.upper(p, in.a, at);
                    ub: long = LONG_MAX;
                    if (self.bConst(p, in, 0)) { ub = self.cv; } else if (in.b != NO_TEMP) { ub = self.upper(p, in.b, at); }
                    if (ua >= 0 && ub >= 0) { hi = bitsBelow(ua | ub); }
                }
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
                r: long = self.rel(p.code[self.first + i].dst);
                if (r < 0 || !self.nonneg.get(r)) { continue; }
                in: Instr = p.code.get(self.first + i);
                if (!self.reach.get(self.blockOf.get(i)) || self.rangeNonneg(r)) { continue; }
                if (!self.yieldsNonneg(p, in, i)) { self.nonneg.set(r, false); going = true; }
            }
        }
    }

    nn &self t:Temp -> bool {
        r: long = self.rel(t);
        return r >= 0 && ((r < self.nonneg.len() && self.nonneg.get(r)) || self.rangeNonneg(r));
    }

    // Temp `r` (relative) has a range, and it is never negative.
    rangeNonneg &self r:long -> bool {
        return self.rOn && self.rLo.get(r) <= self.rHi.get(r) && self.rLo.get(r) >= 0;
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
    // can read s. (`opt.k` does this within a block, for any d written once.) Only between temps
    // of the same type and pointee, so nothing that asks a temp's type sees a different answer.
    // One name for one value is what lets a fact about s decide a test of d.
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

    // ─── block copies of block copies ────────────────────────────────────────

    // `copy A <- B` followed by `copy C <- A`, with nothing writing either in between: the second
    // copy reads B's bytes, so `C <- B` is the same copy. An inlined call that returns an
    // aggregate leaves exactly this. The body builds its value in a slot of its own and copies it
    // into the result scratch the call site gave it (its `$sret`), and the site then copies that
    // scratch to where the value goes (a local, or the caller's own `$sret`). Once the second copy
    // reads B, nothing reads A any more, and `dropDeadSlots` removes the first. Chains collapse in
    // one walk, because a copy forwarded into a slot is recorded with the source it now reads.
    //
    // This works within a block (a label ends what is known), and only between frame slots whose
    // every write is in sight, which means not exposed (`addressConstants`). A slot lent to a call
    // may be written by it, so a call ends what is known about one, and `asm` ends everything. C
    // is never B: a pointer that is no address constant cannot reach a slot that is not exposed.
    forwardCopies &self inout p:IRProgram -> void {
        self.fwDst.clear(); self.fwOff.clear(); self.fwSize.clear(); self.fwSrc.clear(); self.fwSrcRoot.clear();
        for i in 0..self.n {
            ix: long = self.first + i;
            o: IROp = p.code[ix].op;
            if (o == IROp.Label || o == IROp.Asm || o == IROp.Atomic || o == IROp.MemCopy) { self.fwDst.clear(); self.fwOff.clear(); self.fwSize.clear(); self.fwSrc.clear(); self.fwSrcRoot.clear(); continue; }
            if (self.fwDst.len() == 0 && o != IROp.AggCopy) { continue; }
            if (o == IROp.Call || o == IROp.CallIndirect) { self.forgetLent(); continue; }
            if (o == IROp.PtrStore || o == IROp.AggZero) { self.forgetRoot(self.trackedRoot(p.code[ix].a)); continue; }
            if ((o == IROp.Store || o == IROp.ArrStore) && !p.code[ix].isGlobal && p.code[ix].name != NO_SYM) {
                self.forgetRoot(p.code[ix].name as long);
                continue;
            }
            if (o != IROp.AggCopy) { continue; }
            in: Instr = p.code.get(ix);
            dr: long = self.trackedRoot(in.a);
            sr: long = self.trackedRoot(in.b);
            if (sr >= 0) {
                k: long = self.fwFind(sr, self.acOff.get(self.rel(in.b)), in.imm);
                if (k >= 0 && dr != self.fwSrcRoot.get(k)) {
                    in.b = self.fwSrc.get(k);
                    p.code.set(ix, in);
                    sr = self.fwSrcRoot.get(k);
                    self.nForwarded = self.nForwarded + 1;
                }
            }
            self.forgetRoot(dr);
            if (dr >= 0 && sr >= 0 && dr != sr) {
                self.fwDst.push(dr); self.fwOff.push(self.acOff.get(self.rel(in.a))); self.fwSize.push(in.imm);
                self.fwSrc.push(in.b); self.fwSrcRoot.push(sr);
            }
        }
    }

    // The frame slot `t` is an address in, when every write to that slot is in sight; or -1.
    trackedRoot &self t:Temp -> long {
        r: long = self.rel(t);
        if (r < 0 || self.acRoot.get(r) < 0 || self.acKind.get(r) != R_SLOT) { return -1; }
        if (self.exposed.has(self.acRoot.get(r))) { return -1; }
        return self.acRoot.get(r);
    }

    // The copy in force that filled `size` bytes at `off` in slot `root`, or -1.
    fwFind &self root:long off:long size:long -> long {
        for k in 0..self.fwDst.len() {
            if (self.fwDst.get(k) == root && self.fwOff.get(k) == off && self.fwSize.get(k) >= size) { return k; }
        }
        return -1;
    }

    // A write to slot `root`: no copy into it or out of it holds any more.
    forgetRoot &self root:long -> void {
        if (root < 0) { return; }
        k: long = 0;
        while (k < self.fwDst.len()) {
            if (self.fwDst.get(k) == root || self.fwSrcRoot.get(k) == root) { self.fwDrop(k); } else { k = k + 1; }
        }
    }

    // A call: it may write any slot lent to it.
    forgetLent &self -> void {
        k: long = 0;
        while (k < self.fwDst.len()) {
            if (self.lent.has(self.fwDst.get(k)) || self.lent.has(self.fwSrcRoot.get(k))) { self.fwDrop(k); } else { k = k + 1; }
        }
    }

    fwDrop &self k:long -> void {
        last: long = self.fwDst.len() - 1;
        self.fwDst.set(k, self.fwDst.get(last)); self.fwOff.set(k, self.fwOff.get(last)); self.fwSize.set(k, self.fwSize.get(last));
        self.fwSrc.set(k, self.fwSrc.get(last)); self.fwSrcRoot.set(k, self.fwSrcRoot.get(last));
        self.fwDst.pop(); self.fwOff.pop(); self.fwSize.pop(); self.fwSrc.pop(); self.fwSrcRoot.pop();
    }

    // ─── aggregate results built where they go ───────────────────────────────

    // A call returning an aggregate writes it through a hidden pointer into a scratch slot of the
    // caller's, which the caller then copies to where the value goes (`x = f()`, or its own
    // `$sret` for `return f()`). The callee, for its part, builds the value in a slot of its own
    // and copies that to its `$sret`. That is two copies of the whole value per call, and both go:
    //
    // At the call. The scratch's address is read by the call and by one copy out of it, with
    // nothing but address arithmetic between the two, so what the call wrote there is read by that
    // copy alone (even where inlined copies of one body share a scratch number). The copy goes to
    // the start of a frame slot whose every access is in sight (not exposed) and which no call is
    // lent. The callee cannot reach that slot other than through the pointer, so the call is handed
    // the slot itself and the copy goes. Reads of the slot for the arguments (`x = f(x.a)`) are
    // made before the call, so they see the old value. The same goes for the caller's own `$sret`,
    // whose memory nothing this function can name reaches either.
    //
    // In the callee (`buildInPlace`). Every copy into `$sret`, just before a `ret`, reads one frame
    // slot that is not exposed, is as large as the result, and is never accessed by name. That
    // slot then becomes the `$sret` memory: its address is the `$sret` pointer, and the copies go.
    // Writing the result early is safe for the same reason as above: nothing else can see the
    // memory it points at.
    forwardResults &self inout p:IRProgram fname:Sym -> void {
        fillLong(&self.rsUse, self.nt, 0);
        sretT: Temp = NO_TEMP;
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            if (in.op == IROp.Nop) { continue; }
            if (in.op == IROp.Load && in.paramSeed && in.name == intern("$sret")) { sretT = in.dst; }
            self.rsBump(in.a);
            if (!in.bIsImm) { self.rsBump(in.b); }
            for k in 0..in.argCount { self.rsBump(p.args.get(in.firstArg + k)); }
            for k in 0..in.pieceCount { self.rsBump(p.asmVals.get(in.firstPiece + k)); }
        }
        // At each call.
        for i in 0..self.n {
            o: IROp = p.code[self.first + i].op;
            if (o != IROp.Call && o != IROp.CallIndirect) { continue; }
            call: Instr = p.code.get(self.first + i);
            if (call.argCount == 0) { continue; }
            t: Temp = p.args.get(call.firstArg);
            r: long = self.rel(t);
            if (r < 0 || self.defs.get(r) != 1 || self.rsUse.get(r) != 2) { continue; }
            da: long = self.defAt.get(r);
            sl: Instr = p.code.get(self.first + da);
            if (sl.op != IROp.AggSlot || da > i) { continue; }
            size: long = p.aggSlots.get(sl.imm);
            // The copy out of the scratch, with nothing between that touches memory or calls.
            c: long = i + 1;
            while (c < self.n && isAddressArith(p.code[self.first + c].op)) { c = c + 1; }
            if (c >= self.n) { continue; }
            cp: Instr = p.code.get(self.first + c);
            if (cp.op != IROp.AggCopy || cp.b != t || cp.imm != size) { continue; }
            nw: Instr = instr(IROp.Nop);
            if (cp.a == sretT && sretT != NO_TEMP) {
                nw = instr(IROp.Mov);
                nw.a = sretT;
            } else {
                dr: long = self.rel(cp.a);
                if (dr < 0 || self.acKind.get(dr) != R_SLOT || self.acOff.get(dr) != 0) { continue; }
                root: long = self.acRoot.get(dr);
                if (root == AGG_BASE + sl.imm || self.exposed.has(root) || self.lent.has(root)) { continue; }
                // The copy wrote the whole result at the slot's start, so the slot holds it.
                if (root >= AGG_BASE) {
                    nw = instr(IROp.AggSlot);
                    nw.imm = root - AGG_BASE;
                } else {
                    nw = instr(IROp.AddrOf);
                    nw.name = root as Sym;
                }
            }
            nw.dst = t;
            nw.kind = Lit.Ptr;
            p.code.set(self.first + da, nw);
            p.code.set(self.first + c, instr(IROp.Nop));
            self.nResults = self.nResults + 1;
        }
        if (sretT != NO_TEMP) {
            done: long = self.nInPlace;
            self.buildInPlace(p, sretT, fname);
            if (self.nInPlace == done && !gResultEachOff) { self.buildInPlaceEach(p, sretT, fname); }
        }
    }

    rsBump &self t:Temp -> void {
        r: long = self.rel(t);
        if (r >= 0) { self.rsUse.set(r, self.rsUse.get(r) + 1); }
    }

    // The callee's half (see `forwardResults`): one frame slot copied into `$sret` at every return
    // that copies anything becomes the `$sret` memory.
    buildInPlace &self inout p:IRProgram sretT:Temp fname:Sym -> void {
        root: long = -1;
        size: long = 0;
        // The pointer goes nowhere but into those copies and the `ret`s: handed to a call (`return
        // g(&s)` after the call's half) the callee would write the memory it reads.
        uses: long = 0;
        for i in 0..self.n {
            o: IROp = p.code[self.first + i].op;
            if ((o == IROp.AggCopy || o == IROp.Ret) && p.code[self.first + i].a == sretT) { uses = uses + 1; }
        }
        if (uses != self.rsUse.get(self.rel(sretT))) { return; }
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            if (in.op != IROp.AggCopy || in.a != sretT) { continue; }
            // Straight before the `ret` of the same pointer.
            j: long = i + 1;
            while (j < self.n && p.code[self.first + j].op == IROp.Nop) { j = j + 1; }
            if (j >= self.n || p.code[self.first + j].op != IROp.Ret || p.code[self.first + j].a != sretT) { return; }
            sr: long = self.rel(in.b);
            if (sr < 0 || self.acKind.get(sr) != R_SLOT || self.acOff.get(sr) != 0) { return; }
            if (root >= 0 && (self.acRoot.get(sr) != root || in.imm != size)) { return; }
            root = self.acRoot.get(sr);
            size = in.imm;
        }
        if (root < 0 || self.exposed.has(root)) { return; }
        if (root >= AGG_BASE) {
            if (p.aggSlots.get(root - AGG_BASE) != size) { return; }
        } else if (p.fnSlotBytesOf(fname, root as Sym) != size) { return; }
        // Every address of the slot is made by one instruction this rewrites; none by name.
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            if ((in.op == IROp.Load || in.op == IROp.Store || in.op == IROp.ArrLoad || in.op == IROp.ArrStore)
                && !in.isGlobal && in.name != NO_SYM && (in.name as long) == root) { return; }
            if (in.op == IROp.Asm) { return; }
        }
        for i in 0..self.n {
            ix: long = self.first + i;
            in: Instr = p.code.get(ix);
            if (in.op == IROp.AggCopy && in.a == sretT) { p.code.set(ix, instr(IROp.Nop)); continue; }
            makes: bool = (in.op == IROp.AddrOf && !in.isGlobal && in.name != NO_SYM && (in.name as long) == root)
                || (in.op == IROp.AggSlot && AGG_BASE + in.imm == root);
            if (!makes) { continue; }
            mv: Instr = instr(IROp.Mov);
            mv.dst = in.dst;
            mv.a = sretT;
            mv.kind = Lit.Ptr;
            p.code.set(ix, mv);
        }
        self.nInPlace = self.nInPlace + 1;
    }

    // `buildInPlace` where each return copies a slot of its own into `$sret` (`Option.Some(x)` at
    // one and `Option.None` at another): each slot is built in the `$sret` memory, when every
    // access of it lies in the stretch from its first one to its copy, which is entered only at
    // its start and left only through that copy's `ret` (`wcStretchClear`) and touches no other
    // such slot. On every path, then, one slot's bytes are made and returned before any other's
    // are touched, and nothing else reads the memory.
    buildInPlaceEach &self inout p:IRProgram sretT:Temp fname:Sym -> void {
        uses: long = 0;
        for i in 0..self.n {
            o: IROp = p.code[self.first + i].op;
            if ((o == IROp.AggCopy || o == IROp.Ret) && p.code[self.first + i].a == sretT) { uses = uses + 1; }
            if (o == IROp.Asm) { return; }
        }
        if (uses != self.rsUse.get(self.rel(sretT))) { return; }
        roots: Vec<long>;
        at: Vec<long>;
        size: long = -1;
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            if (in.op != IROp.AggCopy || in.a != sretT) { continue; }
            j: long = i + 1;
            while (j < self.n && p.code[self.first + j].op == IROp.Nop) { j = j + 1; }
            if (j >= self.n || p.code[self.first + j].op != IROp.Ret || p.code[self.first + j].a != sretT) { return; }
            sr: long = self.rel(in.b);
            if (sr < 0 || self.acKind.get(sr) != R_SLOT || self.acOff.get(sr) != 0) { return; }
            if (size >= 0 && in.imm != size) { return; }
            size = in.imm;
            r: long = self.acRoot.get(sr);
            for k in 0..roots.len() { if (roots.get(k) == r) { return; } }
            if (self.exposed.has(r) || self.slotBytes(p, fname, r) != size) { return; }
            roots.push(r);
            at.push(i);
        }
        if (roots.len() < 2) { return; }
        self.wcScan(p);
        for k in 0..roots.len() {
            r: long = roots.get(k);
            if (self.wcNamed.has(r)) { return; }
            f: long = self.wcFirst.getOr(r, -1);
            if (f < 0 || self.wcLast.getOr(r, -1) != at.get(k)) { return; }
            for m in 0..roots.len() {
                if (m != k && !self.wcStretchClear(p, f, at.get(k), roots.get(m))) { return; }
            }
        }
        for i in 0..self.n {
            ix: long = self.first + i;
            in: Instr = p.code.get(ix);
            if (in.op == IROp.AggCopy && in.a == sretT) { p.code.set(ix, instr(IROp.Nop)); continue; }
            if (in.op != IROp.AddrOf && in.op != IROp.AggSlot) { continue; }
            mine: bool = false;
            for r in roots {
                if ((in.op == IROp.AddrOf && !in.isGlobal && in.name != NO_SYM && (in.name as long) == r)
                    || (in.op == IROp.AggSlot && AGG_BASE + in.imm == r)) { mine = true; }
            }
            if (!mine) { continue; }
            mv: Instr = instr(IROp.Mov);
            mv.dst = in.dst;
            mv.a = sretT;
            mv.kind = Lit.Ptr;
            p.code.set(ix, mv);
        }
        self.nInPlace = self.nInPlace + 1;
    }

    // What `buildWhereCopied` and `buildInPlaceEach` read: per frame slot, its first and last
    // access (`wcNote`) and whether it is named; per label, where it is and the first and last
    // branch to it.
    wcScan &self inout p:IRProgram -> void {
        self.wcFirst.clear(); self.wcLast.clear(); self.wcNamed.clear();
        self.wcLabel.clear(); self.wcJumpLo.clear(); self.wcJumpHi.clear();
        for i in 0..self.n {
            ix: long = self.first + i;
            o: IROp = p.code[ix].op;
            if (o == IROp.Nop || o == IROp.AggSlot || o == IROp.AddrOf) { continue; }
            if (o == IROp.Label) { self.wcLabel.put(p.code[ix].name as long, i); continue; }
            if (isBranch(o)) {
                k: long = p.code[ix].name as long;
                if (!self.wcJumpLo.has(k)) { self.wcJumpLo.put(k, i); }
                self.wcJumpHi.put(k, i);
            }
            if ((o == IROp.Load || o == IROp.Store || o == IROp.ArrLoad || o == IROp.ArrStore)
                && !p.code[ix].isGlobal && p.code[ix].name != NO_SYM) {
                self.wcNamed.put(p.code[ix].name as long, true);
            }
            // Working out an address from one is no access of the slot.
            if ((o == IROp.Add || o == IROp.Mov || o == IROp.Convert) && self.acOf(p.code[ix].dst) >= 0) { continue; }
            self.wcNote(p.code[ix].a, i);
            if (!p.code[ix].bIsImm) { self.wcNote(p.code[ix].b, i); }
            na: long = p.code[ix].argCount;
            if (na > 0) {
                fa: long = p.code[ix].firstArg;
                for k in 0..na { self.wcNote(p.args.get(fa + k), i); }
            }
            np: long = p.code[ix].pieceCount;
            if (np > 0) {
                fp: long = p.code[ix].firstPiece;
                for k in 0..np { self.wcNote(p.asmVals.get(fp + k), i); }
            }
        }
    }

    // ─── a value built where it is copied ────────────────────────────────────

    // `aggcopy A <- B` copying the whole of frame slot B into the start of slot A, where B's every
    // access comes before the copy and A's none between B's first access and the copy: B's bytes
    // can be A's, and the copy goes. That is a struct literal built in its scratch and copied to
    // the local it initializes (`p: P = P { .. }`, `t = Tree { .. }`), and an inlined callee's
    // returned local copied to where the call's value goes; a chain of them (a value copied on
    // through two scratches) collapses into the last, front to back.
    //
    // Sound because what is between the two ends can neither see A's old bytes nor B's: neither
    // slot is exposed (`addressConstants`, so every access of either is an instruction here with
    // its address as an operand, or one by name, which rules a slot out), and the stretch from
    // B's first access to the copy is entered only at its start and left only at its end: a jump
    // in it lands in it, a label in it is jumped to only from it, and nothing in it returns. So on
    // every path A's old value is dead from B's first access on (the copy overwrites what B
    // covers of it, and nothing reads it before), and B's is dead after the copy. A call in the
    // stretch reaches A only through an address it is handed, which is an access of A. A loop
    // around the whole stretch cannot carry B's value from one trip to the next: the first access
    // in the text is the first on every trip, and a read there would see what no write before it
    // made, which definite initialization rules out.
    buildWhereCopied &self inout p:IRProgram fname:Sym -> void {
        any: bool = false;
        for i in 0..self.n { if (p.code[self.first + i].op == IROp.AggCopy) { any = true; break; } }
        if (!any) { return; }
        self.wcScan(p);
        for c in 0..self.n {
            if (p.code[self.first + c].op != IROp.AggCopy) { continue; }
            in: Instr = p.code.get(self.first + c);
            dr: long = self.rel(in.a);
            sr: long = self.rel(in.b);
            if (dr < 0 || sr < 0 || self.acKind.get(dr) != R_SLOT || self.acKind.get(sr) != R_SLOT) { continue; }
            if (self.acOff.get(dr) != 0 || self.acOff.get(sr) != 0) { continue; }
            a: long = self.acRoot.get(dr);
            b: long = self.acRoot.get(sr);
            if (a < 0 || b < 0 || a == b || self.exposed.has(a) || self.exposed.has(b)) { continue; }
            if (self.wcNamed.has(a) || self.wcNamed.has(b)) { continue; }
            size: long = self.slotBytes(p, fname, b);
            if (size <= 0 || in.imm != size || size > self.slotBytes(p, fname, a)) { continue; }
            f: long = self.wcFirst.getOr(b, -1);
            if (f < 0 || self.wcLast.getOr(b, -1) != c) { continue; }
            if (!self.wcStretchClear(p, f, c, a)) { continue; }
            // B's every address is made by one instruction, which now makes A's.
            for i in 0..self.n {
                ix: long = self.first + i;
                mo: IROp = p.code[ix].op;
                if (mo != IROp.AddrOf && mo != IROp.AggSlot) { continue; }
                m: Instr = p.code.get(ix);
                makes: bool = (m.op == IROp.AddrOf && !m.isGlobal && m.name != NO_SYM && (m.name as long) == b)
                    || (m.op == IROp.AggSlot && AGG_BASE + m.imm == b);
                if (!makes) { continue; }
                nw: Instr = instr(IROp.AggSlot);
                if (a >= AGG_BASE) { nw.imm = a - AGG_BASE; }
                else {
                    nw = instr(IROp.AddrOf);
                    nw.name = a as Sym;
                    nw.structName = m.structName;
                }
                nw.dst = m.dst;
                nw.kind = Lit.Ptr;
                p.code.set(ix, nw);
            }
            p.code.set(self.first + c, instr(IROp.Nop));
            // From here B's accesses are A's, for a later copy out of A.
            for r in 0..self.nt { if (self.acRoot.get(r) == b) { self.acRoot.set(r, a); } }
            if (self.lent.has(b)) { self.lent.put(a, true); }
            if (self.wcFirst.getOr(a, f) >= f) { self.wcFirst.put(a, f); }
            if (self.wcLast.getOr(a, -1) < c) { self.wcLast.put(a, c - 1); }
            self.nBuilt = self.nBuilt + 1;
        }
    }

    // An operand of instruction `i` that is an address in frame slot `t` names: an access of it.
    wcNote &self t:Temp i:long -> void {
        r: long = self.rel(t);
        if (r < 0 || self.acRoot.get(r) < 0 || self.acKind.get(r) != R_SLOT) { return; }
        root: long = self.acRoot.get(r);
        if (!self.wcFirst.has(root)) { self.wcFirst.put(root, i); }
        self.wcLast.put(root, i);
    }

    // Instructions [f, c) touch nothing of slot `a`, and the stretch to the copy at `c` is entered
    // only at `f` and left only at `c`.
    wcStretchClear &self inout p:IRProgram f:long c:long a:long -> bool {
        for i in f..c {
            o: IROp = p.code[self.first + i].op;
            if (o == IROp.Nop || o == IROp.AggSlot || o == IROp.AddrOf) { continue; }
            in: Instr = p.code.get(self.first + i);
            if (o == IROp.Label) {
                k: long = in.name as long;
                if (self.wcJumpLo.has(k) && (self.wcJumpLo.getOr(k, f) < f || self.wcJumpHi.getOr(k, c) > c)) { return false; }
                continue;
            }
            if (isBranch(o)) {
                at: long = self.wcLabel.getOr(in.name as long, -1);
                if (at < f || at > c) { return false; }
            } else if (isTerminator(o) || o == IROp.Asm || o == IROp.RecoverPush) { return false; }
            if (self.acOf(in.a) == a) { return false; }
            if (!in.bIsImm && self.acOf(in.b) == a) { return false; }
            for k in 0..in.argCount { if (self.acOf(p.args.get(in.firstArg + k)) == a) { return false; } }
            for k in 0..in.pieceCount { if (self.acOf(p.asmVals.get(in.firstPiece + k)) == a) { return false; } }
        }
        return true;
    }

    // The bytes frame slot `root` holds: a scratch slot's from the program, a named one's from
    // the function's declarations.
    slotBytes &self inout p:IRProgram fname:Sym root:long -> long {
        if (root >= AGG_BASE) { return p.aggSlots.get(root - AGG_BASE); }
        return p.fnSlotBytesOf(fname, root as Sym);
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
            if (o == IROp.PtrStore || o == IROp.AggCopy || o == IROp.AggZero || o == IROp.Store || o == IROp.MemCopy) { writes = true; break; }
        }
        if (!writes) { return; }
        // The address constants and exposed slots that `collectFacts` found still hold. The
        // rewrites since then (a load become a copy, a computation become a copy of an equal one)
        // never make a new alias of a slot that was not exposed, since a slot whose address was
        // ever stored in memory is exposed already. Code removed since only reads and writes less.
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
                else if (o == IROp.MemCopy) { self.noteSlotRead(p.code[ix].b); }
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
                // A lent slot is read by the calls it is lent to.
                if (self.exposed.has(root) || self.lent.has(root) || self.slotRead.has(root)) { continue; }
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

    // Whether forwarding `v` to the load at `i` is all that would keep `v` across a call (or a
    // `memcpy`, which takes caller-saved registers as a call does): it is written once, one lies
    // between that and `i` in the function's order (`hCall`), and it is read nowhere after it but
    // at `i`. An order, not a path: a heuristic of cost, never of meaning, since the load it keeps
    // is the one the program wrote.
    keptOnlyFor &self inout p:IRProgram v:Temp i:long -> bool {
        r: long = self.rel(v);
        if (r < 0 || self.defs.get(r) != 1 || self.defAt.get(r) < 0) { return false; }
        d: long = self.defAt.get(r);
        if (d >= i) { return false; }
        // A value made of constants and addresses folds, or is made again where it is read, and
        // holds no register across the call.
        if (self.madeAgain(p, v, 0)) { return false; }
        self.hCall = self.callAt.get(i - 1);
        if (self.hCall <= d) { return false; }
        return !self.readAfter(v, self.hCall, i);
    }
    // Whether `t` is computed from constants and addresses alone (through copies and arithmetic,
    // and an address read out of an immutable global's image): what folding turns into a
    // constant, or the emitter makes again. Asked once per temp.
    madeAgain &self inout p:IRProgram t:Temp depth:long -> bool {
        r: long = self.rel(t);
        if (r < 0 || depth > 64 || self.defs.get(r) != 1 || self.defAt.get(r) < 0) { return false; }
        if (self.madeMemo.get(r) != 0) { return self.madeMemo.get(r) == 2; }
        yes: bool = self.madeFrom(p, self.first + self.defAt.get(r), depth);
        if (yes) { self.madeMemo.set(r, 2); } else { self.madeMemo.set(r, 1); }
        return yes;
    }
    madeFrom &self inout p:IRProgram ix:long depth:long -> bool {
        o: IROp = p.code[ix].op;
        if (o == IROp.Const || o == IROp.AddrOf || o == IROp.AggSlot || o == IROp.StrAddr || o == IROp.StrLitVal) { return true; }
        if (o == IROp.PtrLoad && self.roHere && self.roImageOf(p, p.code[ix].dst, 0)) { return true; }
        if (o == IROp.Mov || o == IROp.Convert) { return self.madeAgain(p, p.code[ix].a, depth + 1); }
        if (o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor
            || o == IROp.Shl || o == IROp.Shr) {
            if (!self.madeAgain(p, p.code[ix].a, depth + 1)) { return false; }
            return p.code[ix].bIsImm || self.madeAgain(p, p.code[ix].b, depth + 1);
        }
        return false;
    }
    // Whether `t` is needed after that call anyway: read after it (but at `i`), or a parameter's
    // value, which a function keeps throughout.
    keptAnyway &self inout p:IRProgram t:Temp i:long -> bool {
        r: long = self.rel(t);
        if (r < 0) { return false; }
        if (self.defs.get(r) == 1 && self.defAt.get(r) >= 0) {
            dx: long = self.first + self.defAt.get(r);
            if (p.code[dx].op == IROp.Load && p.code[dx].paramSeed) { return true; }
        }
        return self.readAfter(t, self.hCall, i);
    }
    // Whether `t` is read after position `h` anywhere but at `skip`, from its last two reads.
    readAfter &self t:Temp h:long skip:long -> bool {
        r: long = self.rel(t);
        if (r < 0) { return false; }
        l: long = self.rdLast.get(r);
        if (l > h && l != skip) { return true; }
        return l == skip && self.rdPrev.get(r) > h;
    }
    // The reads `readAfter` asks about, in one pass over the function, and where its calls are.
    noteReads &self inout p:IRProgram -> void {
        fillLong(&self.rdLast, self.nt, -1);
        fillLong(&self.rdPrev, self.nt, -1);
        fillLong(&self.callAt, self.n, -1);
        fillLong(&self.madeMemo, self.nt, 0);
        c: long = -1;
        for j in 0..self.n {
            ix: long = self.first + j;
            o: IROp = p.code[ix].op;
            if ((o == IROp.Call && !p.code[ix].noReturn) || o == IROp.CallIndirect || o == IROp.MemCopy) { c = j; }
            self.callAt.set(j, c);
            if (o == IROp.Nop) { continue; }
            self.readAt(p.code[ix].a, j);
            self.readAt(p.code[ix].x, j);
            if (!p.code[ix].bIsImm) { self.readAt(p.code[ix].b, j); }
            fa: long = p.code[ix].firstArg;
            for k in 0..p.code[ix].argCount { self.readAt(p.args.get(fa + k), j); }
            fp: long = p.code[ix].firstPiece;
            for k in 0..p.code[ix].pieceCount { self.readAt(p.asmVals.get(fp + k), j); }
        }
    }
    // A read of `t` at position `j`, kept if it is among the last two.
    readAt &self t:Temp j:long -> void {
        r: long = self.rel(t);
        if (r < 0) { return; }
        l: long = self.rdLast.get(r);
        if (j == l || j == self.rdPrev.get(r)) { return; }
        if (j > l) { self.rdPrev.set(r, l); self.rdLast.set(r, j); }
        else if (j > self.rdPrev.get(r)) { self.rdPrev.set(r, j); }
    }

    rewrite &self inout p:IRProgram -> void {
        self.noteReads(p);
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
                    // A value kept across a call holds a callee-saved register (or a frame slot) the
                    // whole way; a load at a constant offset from an address that is kept anyway is
                    // cheaper done again than that (`String.write`'s `self.len` around its `memcpy`).
                    if (v != NO_TEMP && o == IROp.PtrLoad && in.x == NO_TEMP && self.keptOnlyFor(p, v, i)
                        && self.keptAnyway(p, in.a, i)) { v = NO_TEMP; }
                    if (v != NO_TEMP) {
                        self.readAt(v, i);
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
                    if (in.imm != BOUNDS_INDEX) { bop = IROp.CmpLe; }
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
                    } else if (k < 1 && in.bIsImm && (in.imm & DIV_NONNEG) == 0) {
                        // By any other constant: truncation and the floor agree, and the emitter
                        // leaves out its rounding toward zero.
                        in.imm = in.imm | DIV_NONNEG;
                        p.code.set(ix, in);
                    }
                } else if (o == IROp.Div && !kindUnsigned(in.kind) && foldableKind(in.kind) && in.bIsImm
                           && log2Exact(in.bImm) >= 1 && self.lowBitsZero(p, in.a, log2Exact(in.bImm), in.kind, at)) {
                    // A dividend whose low k bits are zero is a multiple of 2^k, so the arithmetic
                    // shift is exact and there is nothing to round, whatever its sign: `n / 2`
                    // under `if (n % 2 == 0)`.
                    in.op = IROp.Shr;
                    in.bImm = log2Exact(in.bImm);
                    p.code.set(ix, in);
                    self.nStrength = self.nStrength + 1;
                }
                self.step(p, i, at);
                self.noteCopy(p, i);
            }
        }
    }

    // `x % 2^k` read only by a test against zero: the remainder is zero exactly when x's low k
    // bits are, whatever x's sign, so the mask answers every such test the remainder would. Made
    // before the facts are, so the expression they record is the mask: recorded as `x % 2^k` and
    // rewritten after, its fact handed the mask's value (`x & 1` is 1 where `x % 2` is -1) to a
    // later `x % 2` read as a number.
    maskZeroTests &self inout p:IRProgram -> void {
        for i in 0..self.n {
            ix: long = self.first + i;
            if (p.code[ix].op != IROp.Mod) { continue; }
            in: Instr = p.code.get(ix);
            if (kindUnsigned(in.kind) || !foldableKind(in.kind) || !self.bConst(p, in, 0)) { continue; }
            if (log2Exact(self.cv) < 1 || self.cv - 1 > IMM_HI || !self.zeroTestedOnly(p, in.dst)) { continue; }
            in.op = IROp.BAnd;
            in.bImm = self.cv - 1;
            in.b = NO_TEMP;
            in.bIsImm = true;
            p.code.set(ix, in);
            self.nStrength = self.nStrength + 1;
        }
    }

    // Whether `t`, written once, is read only to be tested against zero for equality: a branch
    // on it (`jz`, or `jcc` with `==`/`!=` 0) or such a comparison made into a value.
    zeroTestedOnly &self inout p:IRProgram t:Temp -> bool {
        r: long = self.rel(t);
        if (r < 0 || self.defs.get(r) != 1) { return false; }
        for i in 0..self.n {
            u: Instr = p.code.get(self.first + i);
            o: IROp = u.op;
            if (o == IROp.Nop || o == IROp.Label) { continue; }
            if (!u.bIsImm && u.b == t) { return false; }
            for k in 0..u.argCount { if (p.args.get(u.firstArg + k) == t) { return false; } }
            for k in 0..u.pieceCount { if (p.asmVals.get(u.firstPiece + k) == t) { return false; } }
            if (u.a != t) { continue; }
            if (o == IROp.Jz) { continue; }
            eq: bool = (o == IROp.Jcc && (u.cmpOp == IROp.CmpEq || u.cmpOp == IROp.CmpNe))
                       || o == IROp.CmpEq || o == IROp.CmpNe;
            if (!eq || !u.bIsImm || u.bImm != 0) { return false; }
        }
        return true;
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
            if (self.fKind.get(f) == F_MEM && self.has(at, f) && self.fA.get(f) != dst) { return self.fA.get(f); }
            f = self.factNext.get(f);
        }
        return NO_TEMP;
    }

    // Whether location `l` holds temp `t` at the point whose facts are at `at`.
    memHolds &self l:long t:Temp at:long -> bool {
        f: long = self.locFactHead.get(l);
        while (f >= 0) {
            if (self.fKind.get(f) == F_MEM && self.fA.get(f) == t && self.has(at, f)) { return true; }
            f = self.factNext.get(f);
        }
        return false;
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

// What may sit between a call and the copy of its result: no memory access, no call.
local isAddressArith o:IROp -> bool {
    return o == IROp.Nop || o == IROp.AddrOf || o == IROp.AggSlot || o == IROp.Const || o == IROp.Mov;
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

pub isArith o:IROp -> bool {
    return o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.Div || o == IROp.Mod
        || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor || o == IROp.Shl || o == IROp.Shr;
}

local isFloatKind k:Lit -> bool { return k == Lit.Float || k == Lit.Double; }

// The types whose values this pass computes with: integers, `bool`, pointers.
// The kinds whose value is the address of a {ptr, len} or {data, vtable} pair.
local pairKind k:Lit -> bool { return k == Lit.Str || k == Lit.Slice || k == Lit.TraitObj; }

local foldableKind k:Lit -> bool {
    return k == Lit.Int || k == Lit.Long || k == Lit.Char || k == Lit.I16 || k == Lit.U8 || k == Lit.U16
        || k == Lit.U32 || k == Lit.U64 || k == Lit.Bool || k == Lit.Ptr || k == Lit.Ref;
}

local convertible k:Lit -> bool { return foldableKind(k) || k == Lit.Struct; }

// How many bytes a value of this type is read and written as (the emitter's `widthOf`), and
// whether it extends with zeroes. `typeInfo` is a hash lookup and these are asked per access, so
// each answer is kept, by tag, the first time it is asked.
local var gKindCode: Vec<long>;

pub kindCode k:Lit -> long {
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

pub kindWidth k:Lit -> long { return kindCode(k) / 2; }
pub kindUnsigned k:Lit -> bool { return kindCode(k) % 2 == 1; }

// What a load of this type leaves in a register depends on its width and on how it extends.
// The least 2^k - 1 at or above `v` (v >= 0): every bit below its highest set.
local bitsBelow v:long -> long {
    m: long = v;
    m = m | (m >> 1);
    m = m | (m >> 2);
    m = m | (m >> 4);
    m = m | (m >> 8);
    m = m | (m >> 16);
    m = m | (m >> 32);
    return m;
}

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

// The smallest value of a type's canonical form.
local kindLo k:Lit -> long {
    w: long = kindWidth(k);
    if (w >= 8) { return LONG_MIN; }
    if (kindUnsigned(k)) { return 0; }
    return 0 - (1 << (w * 8 - 1));
}

// Whether `x + y`, `x - y`, `x * y` leave a 64-bit signed word.
local addWraps x:long y:long -> bool {
    if (y > 0) { return x > LONG_MAX - y; }
    return y < 0 && x < LONG_MIN - y;
}
local subWraps x:long y:long -> bool {
    if (y < 0) { return x > LONG_MAX + y; }
    return y > 0 && x < LONG_MIN + y;
}
local mulWraps x:long y:long -> bool {
    if (x == 0 || y == 0) { return false; }
    if ((x == -1 && y == LONG_MIN) || (y == -1 && x == LONG_MIN)) { return true; }
    q: long = x * y;
    return q / y != x;
}
local min4 a:long b:long c:long d:long -> long {
    m: long = a;
    if (b < m) { m = b; }
    if (c < m) { m = c; }
    if (d < m) { m = d; }
    return m;
}
local max4 a:long b:long c:long d:long -> long {
    m: long = a;
    if (b > m) { m = b; }
    if (c > m) { m = c; }
    if (d > m) { m = d; }
    return m;
}
// The least 2^k - 1 at or above `v` (v >= 0): what an `|` or `^` of values up to v stays under.
local onesAbove v:long -> long {
    m: long = 0;
    while (m < v) { m = (m << 1) | 1; }
    return m;
}

// The largest value of a type's canonical form.
local kindMax k:Lit -> long {
    w: long = kindWidth(k);
    if (w >= 8) { return LONG_MAX; }
    if (kindUnsigned(k)) { return (1 << (w * 8)) - 1; }
    return (1 << (w * 8 - 1)) - 1;
}

// A value as a register of type `k` holds it: the low bytes, extended by the type's signedness.
pub canon k:Lit v:long -> long {
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

// The name whose address temp `t` holds (`promoteLent`'s table by temp), or -1.
local lentAddr addr:Vec<long> base:Temp t:Temp -> long {
    r: long = t - base;
    if (t == NO_TEMP || r < 0 || r >= addr.len()) { return -1; }
    return addr.get(r);
}

// `m[k]`, or `dflt` where there is none (`promoteLent`'s tables).
local lentGet m:HashMap<long, long> k:long dflt:long -> long {
    hit: Option<long> = m.find(k);
    match hit { Some(v) { return v; } None { } }
    return dflt;
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

pub compareHolds op:IROp x:long y:long uns:bool -> bool {
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

// The operations `hoist` moves out of a loop: pure, never faulting (a division only by a constant
// that is neither 0 nor -1), and not a constant, since an integer one rides on its instruction.
// A copy moves only to feed what moved with it (`keepAddresses`).
local hoistableOp o:IROp k:Lit bIsImm:bool bImm:long -> bool {
    if (o == IROp.Const) { return false; }
    if (o == IROp.Mov) { return !isAggregate(k); }
    if (o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.BAnd || o == IROp.BOr
        || o == IROp.BXor || o == IROp.Shl || o == IROp.Shr || o == IROp.BNot || o == IROp.Convert || isCompare(o)) {
        return !isAggregate(k);
    }
    if (o == IROp.Div || o == IROp.Mod) { return isFloatKind(k) || (bIsImm && bImm != 0 && bImm != -1); }
    if (o == IROp.AddrOf || o == IROp.StrAddr || o == IROp.FnAddr || o == IROp.VtableAddr) { return true; }
    if (o == IROp.PtrLoad || o == IROp.Load) { return !isAggregate(k); }
    return false;
}

// Whether a pointer is laid anywhere in bytes [off, off + w) of image `img`.
local relocWithin inout p:IRProgram img:long off:long w:long -> bool {
    f: long = p.imageRelocFirst.get(img);
    for q in f..f + p.imageRelocCount.get(img) {
        o: long = p.relocOffset.get(q);
        if (o < off + w && off < o + 8) { return true; }
    }
    return false;
}

// ─── a moved argument's bytes, owned where they lie ─────────────────────────

// A struct or tuple parameter taken by value arrives as the address of the caller's bytes, and
// the prologue copies them into the callee's own slot (`asm.k` `emitSeeds`), so that writing the
// parameter cannot write the caller's value and nothing the caller does can change it. When every
// call hands the parameter bytes nothing reads again (a `Call`'s `scale`, which `Lowerer.freshArg`
// marks: a value built for the call, or an owning local the call moves and no other argument
// names), the copy protects nothing, and the callee owns those bytes where they lie: the
// parameter becomes the pointer it arrived as, its seed a borrow's, `&` of it that pointer.
// Writing it writes the caller's frame where nothing reads after the call: a scratch slot only
// the call knows, or a moved local the checker holds unread until it is assigned again.
//
// It runs once the inliner is done (`Flow.run`), so a call it spliced away is no call to ask
// about and no body becomes inlinable that was not. Only where every call is in sight: a
// whole-program build (not `--lib`, `--use` or a package build), a function no fn value or vtable
// may hold (an addressed one, any implementation's method, one a folded global's image points
// at), none an `asm` block calls by its label, not one read from a `.klib`, and every call to it
// direct. A call the lowerer made any way but `lowerCall` marks nothing fresh, so its callee keeps
// the copy.
local ownMovedArgs inout p:IRProgram -> void {
    if (gMovedArgsOff || gKlibMode || gOpenObject) { return; }
    // Each function's candidates, as a mask of IR positions: a seed of a struct or tuple taken by
    // value, which the body names only through `&` (anything else keeps the slot a value).
    fnAt: HashMap<long, long>;
    cand: Vec<long>;
    any: bool = false;
    for f in 0..p.funcs.len() {
        m: long = 0;
        if (!p.funcs[f].imported && !p.funcs[f].isMain && p.funcs[f].instrCount > 0
            && !gReg.isImplFn(p.funcs[f].name)) {
            first: long = p.funcs[f].firstInstr;
            seeds: long = 0;
            while (seeds < p.funcs[f].instrCount && seeds < 62) {
                ix: long = first + seeds;
                if (p.code[ix].op != IROp.Load || !p.code[ix].paramSeed) { break; }
                if (p.code[ix].imm > 0 && byValueAggregate(p.code[ix].kind) && p.code[ix].dst != NO_TEMP) { m = m | (1 << seeds); }
                seeds = seeds + 1;
            }
            if (m != 0) { m = m & ~namedOtherwise(p, p.funcs.get(f), seeds, m); }
        }
        cand.push(m);
        if (m != 0) { any = true; fnAt.put(p.funcs[f].name as long, f); }
    }
    if (!any) { return; }
    // One that something other than a direct call may reach, or whose name another function has.
    for f in 0..p.funcs.len() {
        at: long = fnAt.getOr(p.funcs[f].name as long, -1);
        if (at >= 0 && at != f) { fnAt.put(p.funcs[f].name as long, -1); }
    }
    for n in gAddressedFns { if (fnAt.has(n as long)) { fnAt.put(n as long, -1); } }
    for i in 0..p.relocKind.len() {
        if (p.relocKind.get(i) == RelocKind.Fn && fnAt.has(p.relocTarget.get(i))) { fnAt.put(p.relocTarget.get(i), -1); }
    }
    // Every call has to hand each candidate fresh bytes. One walk over the program, which also
    // finds any address taken that the checker did not note, and any label an `asm` block spells.
    sites: Vec<long>;
    spelled: Vec<Sym>;
    for i in 0..p.code.len() {
        o: IROp = p.code[i].op;
        if (o == IROp.FnAddr) {
            if (fnAt.has(p.code[i].name as long)) { fnAt.put(p.code[i].name as long, -1); }
            continue;
        }
        if (o == IROp.Asm) {
            fp: long = p.code[i].firstPiece;
            for q in 0..p.code[i].pieceCount {
                if (p.asmKinds.get(fp + q) == AsmKind.Text && strContains(nameOf(p.asmText.get(fp + q)), "mfn_")) { spelled.push(p.asmText.get(fp + q)); }
            }
            continue;
        }
        if (o != IROp.Call) { continue; }
        f: long = fnAt.getOr(p.code[i].name as long, -1);
        if (f < 0) { continue; }
        keep: long = p.code[i].scale & CALL_FRESH_ALL;
        na: long = p.code[i].argCount;
        if (na < 62) { keep = keep & ((1 << na) - 1); }
        cand.set(f, cand.get(f) & keep);
        sites.push(i);
    }
    // What stays: a pointer each, and every call told the callee may write there.
    for f in 0..p.funcs.len() {
        m: long = cand.get(f);
        if (m == 0 || fnAt.getOr(p.funcs.get(f).name as long, -1) != f) { continue; }
        // A call an `asm` block makes by the label is no call in sight.
        if (spelled.len() > 0) {
            lab: str = fnLabelOf(p.funcs[f].name);
            hid: bool = false;
            for t in spelled { if (strContains(nameOf(t), lab)) { hid = true; } }
            if (hid) { cand.set(f, 0); continue; }
        }
        fn: IRFunc = p.funcs.get(f);
        for k in 0..62 {
            if ((m & (1 << k)) == 0) { continue; }
            s: Instr = p.code.get(fn.firstInstr + k);
            s.kind = Lit.Ref;
            s.imm = 0;
            p.code.set(fn.firstInstr + k, s);
            p.tempKinds.set(s.dst, Lit.Ref);
            for i in fn.firstInstr + k + 1..fn.firstInstr + fn.instrCount {
                if (p.code[i].op != IROp.AddrOf || p.code[i].isGlobal || p.code[i].name != s.name) { continue; }
                in: Instr = p.code.get(i);
                mv: Instr = instr(IROp.Mov);
                mv.dst = in.dst;
                mv.a = s.dst;
                mv.kind = in.kind;
                mv.structName = in.structName;
                p.code.set(i, mv);
            }
        }
        fn.borrows = fn.borrows | m;
        p.funcs.set(f, fn);
        gMovedParams = gMovedParams + paramsIn(m);
    }
    for i in sites {
        f: long = fnAt.getOr(p.code[i].name as long, -1);
        if (f < 0 || cand.get(f) == 0 || (p.code[i].imm & CALL_KNOWN) == 0) { continue; }
        in: Instr = p.code.get(i);
        for k in 0..CALL_ARGS { if ((cand.get(f) & (1 << k)) != 0) { in.imm = in.imm | (1 << (CALL_ARGS + k)); } }
        p.code.set(i, in);
    }
}
// How many parameters `ownMovedArgs` gave their callers' bytes, for `--trace-opt`.
local var gMovedParams: long = 0;

// Which of the seeds in `m` the body of `fn` names other than through `&`: a load or store of the
// slot by name, an element of it, a name an `asm` block spells.
local namedOtherwise inout p:IRProgram fn:IRFunc seeds:long m:long -> long {
    out: long = 0;
    for i in fn.firstInstr + seeds..fn.firstInstr + fn.instrCount {
        o: IROp = p.code[i].op;
        if (o != IROp.Load && o != IROp.Store && o != IROp.ArrLoad && o != IROp.ArrStore && o != IROp.Asm) { continue; }
        for k in 0..seeds {
            if ((m & (1 << k)) == 0) { continue; }
            nm: Sym = p.code[fn.firstInstr + k].name;
            if (o == IROp.Asm) {
                fp: long = p.code[i].firstPiece;
                for q in 0..p.code[i].pieceCount { if (p.asmNames.get(fp + q) == nm) { out = out | (1 << k); } }
            } else if (!p.code[i].isGlobal && p.code[i].name == nm) { out = out | (1 << k); }
        }
    }
    return out;
}
local paramsIn m0:long -> long {
    m: long = m0;
    n: long = 0;
    while (m != 0) { m = m & (m - 1); n = n + 1; }
    return n;
}
