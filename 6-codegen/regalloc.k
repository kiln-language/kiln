// Linear-scan register allocation over one function's temps.
//
// Live ranges come from real liveness over the control-flow graph, so a value can stay in a
// register across a loop's back edge. A range is one span rather than a list of holes, which is
// conservative but never wrong. A temp live across a call (`liveAcross`: live after it, which a
// call inside its span need not be) takes a register the call leaves alone: a caller-saved one
// outside what the call may change (`siteMask`: for a call to a function already written, what
// its text may change), a callee-saved one, or a caller-saved one with a home in the frame that it
// is read back from after each call that changes it (`homed`); or the frame.
#include <{cfg, ir}>
#include <parse::upstream>
#include <support::compiler>
#include <stdlib::{map, option, vec}>

pub SPILLED: long = -1;

// `--no-exact-calls`: a range crosses a call when a call lies anywhere inside its span, live
// across it or not (`liveAcross`).
pub var gExactCallsOff: bool = false;
// `--no-second-chance`: a range left without a register stays so (`secondChance`).
pub var gSecondChanceOff: bool = false;
// `--no-homes`: a range live across a call takes a callee-saved register or the frame, never a
// caller-saved register with a home (`homed`).
pub var gHomesOff: bool = false;
// A homed temp written to its home just before the calls it is live across, where it may have
// changed since its home last held it, instead of at every write (`--no-sink-homes`).
pub var gSinkHomesOff: bool = false;
// `--no-commute`: a result takes its left operand's register only, never the right one's (`takeOperandReg`).
pub var gCommuteOff: bool = false;
// `--no-ipra`: a call changes every caller-saved register, whatever its callee is (`siteMask`).
pub var gIpraOff: bool = false;
// `--ipra-asm-full`: a function holding an `asm` block may change every caller-saved register,
// whatever its lines say (asm.k, `finishMask`).
pub var gIpraAsmFull: bool = false;

// The physical register numbering the whole back end works in, named here because this is the
// module `asm.k` includes rather than the other way round. `regNames` in asm.k spells these by
// index, so the order below and the order it builds have to agree; `checkRegNumbering` in asm.k
// checks that when the compiler is built.
pub REG_RAX: long = 0;
pub REG_RBX: long = 1;
pub REG_RCX: long = 2;
pub REG_RDX: long = 3;
pub REG_RDI: long = 4;
pub REG_RSI: long = 5;
pub REG_R8:  long = 6;
pub REG_R9:  long = 7;
pub REG_R10: long = 8;
pub REG_R11: long = 9;
pub REG_R12: long = 10;
pub REG_R13: long = 11;
pub REG_R14: long = 12;
pub REG_R15: long = 13;

// `rax` and `rdx` are reserved scratch and never allocated, so the allocatable caller-saved set is
// the other six of the first eight plus `r10` and `r11`, and the callee-saved set is `r12` to
// `r15`.
pub CALLER_SAVED_COUNT: long = 8;
pub CALLEE_SAVED_COUNT: long = 4;

// How many floats pass in `xmm` registers, and how many other arguments in general ones (this
// compiler's order: `rax`, `rbx`, `rcx`, `rdx`, `rdi`, `rsi`, `r8`-`r11`, every caller-saved
// register); what is past either goes on the stack.
pub FLOAT_ARG_REGS: long = 8;
pub INT_ARG_REGS: long = 10;

pub callerSavedAt i:long -> long {
    if (i == 0) { return REG_RBX; }
    if (i == 1) { return REG_RCX; }
    if (i == 2) { return REG_RDI; }
    if (i == 3) { return REG_RSI; }
    if (i == 4) { return REG_R8; }
    if (i == 5) { return REG_R9; }
    if (i == 6) { return REG_R10; }
    return REG_R11;
}
pub calleeSavedAt i:long -> long { return REG_R12 + i; }

pub isCalleeSaved r:long -> bool {
    return (r >= REG_R12 && r <= REG_R15) || (r >= REG_XMM12 && r < REG_SLOTS);
}

// Floats get a register class of their own, `xmm8` to `xmm14`, numbered after the general
// registers. (`xmm0` to `xmm7` carry float arguments, `xmm0` and `xmm1` are the scratch of every
// float operation, and `xmm15` is a block copy's.) `xmm8` to `xmm11` are caller-saved, as every
// `xmm` register is in System V. `xmm12` to `xmm14` are callee-saved between Kiln functions: a
// function that uses one saves its low eight bytes (all a scalar float occupies) in its frame, so
// a float live across a call can stay in one, just as an integer stays in `r12` to `r15`. An
// `asm` block must leave them alone, as it must leave `r12` to `r15`; a C caller of an exported
// function assumes them clobbered anyway and loses nothing.
//
// A call that may reach foreign code does not keep them (`clobbersXmm`). That is a direct call
// to a function declared without a body (another object's, perhaps C's, where System V lets the
// callee clobber every `xmm` register), and a call through a pointer wherever foreign code may
// be what it holds: in a program that declares such a function, and in an object others link
// to (`--lib`, `--use`, a package), which can hand it a pointer to anything. A float live across
// one of those is held as its bits in a general callee-saved register or in the frame. And a
// function that makes one keeps the three for its own caller, which may hold floats in them
// across the call to it: it saves them in its frame as if it used them (`reachesForeign`).
pub REG_XMM8: long = 14;
pub XMM_COUNT: long = 7;
pub XMM_CALLER_COUNT: long = 4;
pub REG_XMM12: long = 18;
pub REG_SLOTS: long = 21;      // general and `xmm` registers together, the size of per-register tables
pub isXmm r:long -> bool { return r >= REG_XMM8 && r < REG_SLOTS; }

// What a call may change, as a set of registers: bit `r` for register `r` above, and bit
// REG_SLOTS for the `xmm` registers nothing is allocated to, counted as one (relax.k's RX_*
// count the same way). Every call changes the scratch (`MASK_SCRATCH`); one whose callee is
// unknown, may reach foreign code, or is an `asm` block or a `memcpy` changes every register a
// callee need not keep (`MASK_FULL`). A direct call to a function already written changes what
// that function's text may change (`RegAlloc.fnMask`), the registers its arguments are passed in
// and the scratch, and a value may stay in any other caller-saved register across it.
pub MASK_FULL: long = maskFull();
pub MASK_SCRATCH: long = (1 << REG_RAX) | (1 << REG_RDX) | (1 << REG_SLOTS);
local maskFull -> long {
    m: long = 0;
    for r in 0..REG_SLOTS + 1 { if (!isCalleeSaved(r)) { m = m | (1 << r); } }
    return m;
}

// One temp's live range, and whether it has to survive a call.
// `weight` is what spilling it would cost: its reads and writes, each counted by how deeply it
// sits in loops.
// `xmm`: the temp is a float whose every use the emitter can serve from an `xmm` register.
// `remat`: the temp's value can be computed again wherever it is read (`RegAlloc.remat`), so
// spilling it costs no store and no slot.
pub struct Interval { temp: Temp, start: long, end: long, crossesCall: bool, weight: long, xmm: bool, remat: bool }

// Whether a range keeps its value in register `r` across everything it is live across, given what
// those may change (`RegAlloc.clobOf`).
pub survives clob:long r:long -> bool { return (clob & (1 << r)) == 0; }

// The caller-saved general registers a value may be allocated to, as a set.
pub MASK_CALLER_GPR: long = (1 << REG_RBX) | (1 << REG_RCX) | (1 << REG_RDI) | (1 << REG_RSI) | (1 << REG_R8) | (1 << REG_R9) | (1 << REG_R10) | (1 << REG_R11);
pub MASK_CALLER_XMM: long = (1 << REG_XMM8) | (1 << (REG_XMM8 + 1)) | (1 << (REG_XMM8 + 2)) | (1 << (REG_XMM8 + 3));

// The kinds of rematerializable temp (`RegAlloc.rematKind`). Such a temp is written once, by an
// instruction that reads nothing but its own fields, so the emitter may compute it again at every
// read instead of keeping it anywhere: a constant (an integer's or a float's bits), or the
// address of a named slot, a global, a hidden aggregate slot or a string literal.
pub REMAT_NONE: long = 0;
pub REMAT_CONST: long = 1;
pub REMAT_ADDR: long = 2;
pub REMAT_AGG: long = 3;
pub REMAT_STR: long = 4;

pub struct RegAlloc {
    // Indexed by a temp's position within this function: `t - base`. Temps are numbered across
    // the whole program, so indexing by the temp id would give every function an entry for every
    // temp in the program, each of them SPILLED and each then handed eight bytes of frame by the
    // emitter.
    tempReg: Vec<long>,          // physical register per temp of this function, or SPILLED
    base: Temp,                  // this function's first temp; `Interval.temp` is relative to it
    usedCallee: Vec<bool>,       // which callee-saved registers the prologue must save
    intervals: Vec<Interval>,
    active: Vec<Interval>,       // currently assigned, kept sorted by end ascending
    freeRegs: Vec<bool>,         // indexed by physical register
    endOf: Vec<long>,            // per temp of this function, where its range ends (-1: none)
    startOf: Vec<long>,          // ...and where it starts
    xmmOk: Vec<bool>,            // per temp: a float every instruction touching it handles in `xmm`
    rematKind: Vec<long>,        // per temp: REMAT_*, what computes it again (`remat`)
    rematDef: Vec<long>,         // per temp: its one definition, an index into the function's run
    argOnly: Vec<bool>,          // per temp: computed again where each read takes it (`markArgOnly`)
    fused: Vec<bool>,            // per temp: computed only as the next branch's comparison (`markFused`)
    fusedAt: Vec<long>,          // ...and that branch's index in the function's run
    // Per temp: live into a `recover` handler, so kept in the frame for its whole range. A `raise`
    // arrives with only rsp and rbp put back; no register still holds what it held at the call.
    inFrame: Vec<bool>,
    // Per temp: what the calls, `asm` blocks and `memcpy`s it is live across may change, the
    // union of their `siteMask`s (`liveAcross`); none for a temp live across none of them, since
    // every one changes the scratch.
    across: Vec<long>,
    xAcross: Vec<bool>,          // ...live across a call that may reach foreign code
    // A temp live across calls kept in a caller-saved register all the same (`homed`): it has a
    // slot too, its home, written wherever the temp is, and read back into the register after
    // each call it is live across. Per clobbering instruction, the temps live across it, as a run
    // in `crossList` (`crossFirst`, -1 for an instruction that clobbers nothing, `crossCount`).
    homed: Vec<bool>,
    crossFirst: Vec<long>, crossCount: Vec<long>, crossList: Vec<long>,
    crossStore: Vec<bool>,       // per entry of `crossList`: the temp may have changed since its home
                                 // last held it, so it is written there before that instruction
    defW: Vec<long>,             // per temp: its writes, weighted as `weight` is
    crossW: Vec<long>,           // ...and the calls it is live across, weighted the same way
    foreign: HashMap<long, bool>,   // the program's functions declared without a body
    foreignN: long,                 // ...built from this many of `IRProgram.externs`
    anyForeign: bool,               // a call through a pointer may reach foreign code (`clobbersXmm`)
    // What each function already written may change (its name -> a set as MASK_FULL is), filled
    // in by the emitter as it finishes each (`siteMask`).
    fnMask: HashMap<long, long>
}

methods RegAlloc for Default {
    new -> RegAlloc {
        return RegAlloc { tempReg: vec![], base: 0, usedCallee: vec![], intervals: vec![], active: vec![],
                          freeRegs: vec![], endOf: vec![], startOf: vec![], xmmOk: vec![], rematKind: vec![], rematDef: vec![], argOnly: vec![],
                          fused: vec![], fusedAt: vec![], inFrame: vec![], across: vec![], xAcross: vec![], homed: vec![], crossFirst: vec![], crossCount: vec![], crossList: vec![], crossStore: vec![], defW: vec![], crossW: vec![],
                          foreign: map![], foreignN: -1, anyForeign: true, fnMask: map![] };
    }
}

methods RegAlloc {
    allocate &self p:IRProgram fn:IRFunc -> void {
        self.base = fn.firstTemp;
        n: long = fn.tempCount - fn.firstTemp;
        if (n < 0) { n = 0; }
        self.tempReg.clear();
        self.intervals.clear();
        self.active.clear();
        for i in 0..n { self.tempReg.push(SPILLED); }
        self.homed.clear();
        for i in 0..n { self.homed.push(false); }
        self.crossFirst.clear();
        self.usedCallee.clear();
        for i in 0..REG_SLOTS { self.usedCallee.push(false); }
        if (n == 0) { return; }

        self.computeIntervals(p, fn);
        self.sortByStart();
        self.markRaxPairs(p, fn);
        self.markArgOnly(p, fn);
        self.markFused(p, fn);

        self.freeRegs.clear();
        for i in 0..REG_SLOTS { self.freeRegs.push(false); }
        for i in 0..CALLER_SAVED_COUNT { self.freeRegs.set(callerSavedAt(i), true); }
        for i in 0..XMM_COUNT { self.freeRegs.set(REG_XMM8 + i, true); }
        for i in 0..CALLEE_SAVED_COUNT { self.freeRegs.set(calleeSavedAt(i), true); }

        for k in 0..self.intervals.len() {
            cur: Interval = self.intervals.get(k);
            if (fn.holdsRecover && self.inFrame.get(cur.temp)) { self.tempReg.set(cur.temp, SPILLED); continue; }
            if (self.tempReg.get(cur.temp) == REG_RAX || self.argOnly.get(cur.temp) || self.fused.get(cur.temp)) { continue; }
            self.expireBefore(cur.start);
            if (self.takeOperandReg(p, fn, cur)) { continue; }
            reg: long = self.pickRegister(cur, self.handedOn(p, fn, cur));
            if (reg != SPILLED) { self.assign(cur, reg); }
            else { self.spillAround(cur); }
        }
        if (!gSecondChanceOff) { self.secondChance(fn); }
        if (self.reachesForeign(p, fn)) {
            for x in REG_XMM12..REG_SLOTS { self.usedCallee.set(x, true); }
        }
    }

    // Whether a call in this function may reach foreign code (`clobbersXmm`), which need not keep
    // `xmm12` to `xmm14`; this function's caller relies on them all the same. (An `asm` block must
    // leave them alone, as it must `r12` to `r15`.)
    reachesForeign &self p:IRProgram fn:IRFunc -> bool {
        for i in 0..fn.instrCount {
            if (self.clobbersXmm(p, fn.firstInstr + i)) { return true; }
        }
        return false;
    }

    // A temp left without a register, retried once the scan is done: a register the scan gave
    // away and later took back (`spillAround`) may be free over its whole range. Heaviest first.
    secondChance &self fn:IRFunc -> void {
        cand: Vec<long>;
        // What each register holds, as runs by register (`occFirst`, `occCount`) of the ranges'
        // ends in `occS` and `occE`, and what this pass gives out after them (`addS`, `addE`, `addR`).
        occFirst: Vec<long>; occCount: Vec<long>; occS: Vec<long>; occE: Vec<long>;
        addS: Vec<long>; addE: Vec<long>; addR: Vec<long>;
        for r in 0..REG_SLOTS { occFirst.push(0); occCount.push(0); }
        for k in 0..self.intervals.len() {
            iv: Interval = self.intervals.get(k);
            r: long = self.tempReg.get(iv.temp);
            if (r != SPILLED) {
                if (r != REG_RAX) { occCount.set(r, occCount.get(r) + 1); }
                continue;
            }
            if (fn.holdsRecover && self.inFrame.get(iv.temp)) { continue; }
            if (self.argOnly.get(iv.temp) || self.fused.get(iv.temp)) { continue; }
            cand.push(k);
        }
        if (cand.len() == 0) { return; }
        at: long = 0;
        for r in 0..REG_SLOTS { occFirst.set(r, at); at = at + occCount.get(r); occCount.set(r, 0); }
        for k in 0..at { occS.push(0); occE.push(0); }
        for k in 0..self.intervals.len() {
            iv: Interval = self.intervals.get(k);
            r: long = self.tempReg.get(iv.temp);
            if (r == SPILLED || r == REG_RAX) { continue; }
            j: long = occFirst.get(r) + occCount.get(r);
            occS.set(j, iv.start);
            occE.set(j, iv.end);
            occCount.set(r, occCount.get(r) + 1);
        }
        // Heaviest first (insertion sort: few).
        for a in 1..cand.len() {
            x: long = cand.get(a);
            j: long = a;
            while (j > 0 && self.intervals.get(cand.get(j - 1)).weight < self.intervals.get(x).weight) {
                cand.set(j, cand.get(j - 1));
                j = j - 1;
            }
            cand.set(j, x);
        }
        // First a register that keeps the value as it is (`survives`), then, for a range live
        // across calls, a caller-saved one with a home.
        for c in cand {
            iv: Interval = self.intervals.get(c);
            cm: long = self.clobOf(iv.temp, iv.crossesCall);
            done: bool = false;
            for pass in 0..2 {
                if (done) { break; }
                for q in 0..REG_SLOTS {
                    r: long = choiceAt(q, iv.crossesCall);
                    if (r < 0) { continue; }
                    keeps: bool = survives(cm, r);
                    if (pass == 0 && !keeps) { continue; }
                    if (pass == 1 && (keeps || isXmm(r) || !self.homeable(iv))) { continue; }
                    if (isXmm(r) && !iv.xmm) { continue; }
                    free: bool = true;
                    f: long = occFirst.get(r);
                    for o in f..f + occCount.get(r) {
                        if (occS.get(o) <= iv.end && iv.start <= occE.get(o)) { free = false; break; }
                    }
                    if (free) {
                        for o in 0..addR.len() {
                            if (addR.get(o) == r && addS.get(o) <= iv.end && iv.start <= addE.get(o)) { free = false; break; }
                        }
                    }
                    if (!free) { continue; }
                    self.tempReg.set(iv.temp, r);
                    if (!keeps) { self.homed.set(iv.temp, true); }
                    if (isCalleeSaved(r)) { self.usedCallee.set(r, true); }
                    addS.push(iv.start); addE.push(iv.end); addR.push(r);
                    done = true;
                    break;
                }
            }
        }
    }

    // For `d = op a, ...` where this is the last read of `a`, `d` takes over `a`'s register as `a`
    // lets go of it, and the emitter's `mov d, a` before a two-operand instruction disappears.
    // This is done only for instructions whose emitter reads every operand before it writes the
    // destination (each computes in `rax`/`rdx`, or in the destination starting from the left
    // operand), and only where `d`'s range starts at this definition, so no part of `d` lives
    // before it.
    takeOperandReg &self p:IRProgram fn:IRFunc cur:Interval -> bool {
        in: Instr = p.code.get(fn.firstInstr + cur.start);
        if (in.dst - self.base != cur.temp || in.a == NO_TEMP || in.a == in.dst) { return false; }
        if (!sharesOperandReg(in.op)) { return false; }
        if (self.takeReg(cur, in.a - self.base)) { return true; }
        // An operation whose operands may be swapped takes the right one's instead: `b = a ^ t`
        // with `t` dying there is `xor t, a`, no copy of `a` first.
        if (gCommuteOff || in.bIsImm || in.b == NO_TEMP || in.b == in.a || in.b == in.dst) { return false; }
        if (!(in.op == IROp.Add || in.op == IROp.Mul || in.op == IROp.BAnd || in.op == IROp.BOr || in.op == IROp.BXor)) { return false; }
        if (isFloatLit(in.kind)) { return false; }
        return self.takeReg(cur, in.b - self.base);
    }

    // `cur` takes over the register of `ra` (this function's numbering), whose range ends where
    // `cur`'s starts.
    takeReg &self cur:Interval ra:long -> bool {
        if (ra < 0 || ra >= self.tempReg.len() || self.endOf.get(ra) != cur.start) { return false; }
        reg: long = self.tempReg.get(ra);
        if (reg == SPILLED || reg == REG_RAX || !survives(self.clobOf(cur.temp, cur.crossesCall), reg)) { return false; }
        if (isXmm(reg) && !cur.xmm) { return false; }
        for i in 0..self.active.len() {
            if (self.active.get(i).temp == ra) {
                self.active.removeAt(i);
                self.freeRegs.set(reg, true);
                self.assign(cur, reg);
                return true;
            }
        }
        return false;
    }

    // `rax` is the emitter's scratch, never allocated for long, but a value that is written by
    // one instruction and read only by the next one emitted (deleted instructions between) can
    // live there: the scratch is free in between, since nothing is emitted there. It is worth it
    // where the value has to pass through `rax` anyway: a call's result (`t = f(x)`, then
    // `u = a + t`, `if (t)`, `return t`), and a value computed for a return or for a call's first
    // argument (`return a + b`, `f(n - 1)`). Each saves a copy into or out of `rax`. Between two
    // other instructions it would cost one instead, since `t = a ^ b` then `u = t + c` is
    // computed in place in `a`'s register when `a` dies there.
    //
    // The writer must leave its result in its destination last, after any use it makes of the
    // scratch, and the reader must read that operand before it writes `rax` or fetches anything
    // else into it. Each instruction below was checked against its emitter for that:
    // - writers: a call (`callResult` then leaves the result where it is), a copy, `+ - * & | ^`,
    //   a load, a load through a pointer, an integer conversion;
    // - readers: a return; a direct call taking the value as its first argument (which goes in
    //   `rax`, or, should its class be a float's, is moved to `xmm0` before any general register
    //   is written), with every argument in a register (a stack argument is staged through
    //   `rax`); `+ - * & | ^` on either side (`emitArith` fetches the left operand into `rdx` when
    //   the right one is in `rax`, and computes in `rdx` when both the right operand and the
    //   result would be there); a copy, a conversion and a store; a branch, a load or a store
    //   through a pointer and a bounds check, each only with the value as the operand read first
    //   (`a`), since a later operand that has to be fetched is fetched into `rax`.
    // A reader may also be the next value's writer (`return f(g(x))`): it reads its operand before
    // it writes the result, so two such values never meet in `rax`. Integers only: a float is read
    // from or into its own `xmm` register.
    markRaxPairs &self p:IRProgram fn:IRFunc -> void {
        for k in 0..self.intervals.len() {
            cur: Interval = self.intervals.get(k);
            s: long = cur.start;
            e: long = cur.end;
            if (e <= s || self.rematDef.get(cur.temp) != s) { continue; }
            j: long = s + 1;
            while (j < e && p.code[fn.firstInstr + j].op == IROp.Nop) { j = j + 1; }
            if (j != e) { continue; }
            t: Temp = self.base + cur.temp;
            kt: Lit = p.kindOf(t);
            if (kt == Lit.Void || isFloatLit(kt)
                || (isAggregate(kt) && kt != Lit.Str && kt != Lit.Slice && kt != Lit.TraitObj)) { continue; }
            w: Instr = p.code.get(fn.firstInstr + s);
            r: Instr = p.code.get(fn.firstInstr + e);
            if (!raxWriter(w) || !raxReader(p, r, t)) { continue; }
            if (w.op != IROp.Call && w.op != IROp.CallIndirect && r.op != IROp.Ret && r.op != IROp.Call) { continue; }
            self.tempReg.set(cur.temp, REG_RAX);
        }
    }

    // A constant or an address (`markRemat`) whose every read the emitter computes in place is
    // given no register, which stays free for the values that need one:
    // - a call's argument: the call's parallel move computes it straight into the argument's own
    //   register (`materialize`), one instruction where a register would cost two (computing it,
    //   then the move);
    // - a store's value, when it is a constant the store can carry as its immediate
    //   (`storesImmediate`): `mov dword [rdi + rcx*4], 1`;
    // - a load's or a store's base, when it is a frame slot's address or (with no index) a
    //   global's (`addressInPlace`): `[rbp + rcx*4 - 400000]`, `[rel g + 8]`;
    // - the length a bounds check compares with, when it is a constant that fits the compare's
    //   sign-extended 32-bit immediate (`immediateIn`): `cmp rcx, 1000`.
    // Where it is read any other way it is an ordinary temp, given a register if one is free.
    markArgOnly &self p:IRProgram fn:IRFunc -> void {
        n: long = self.tempReg.len();
        self.argOnly.clear();
        for t in 0..n { self.argOnly.push(self.rematKind.get(t) != REMAT_NONE); }
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (in.op == IROp.Nop || in.op == IROp.Label) { continue; }
            access: bool = in.op == IROp.PtrLoad || in.op == IROp.PtrStore;
            if (!access || !self.addressInPlace(p, fn, in.a, in.x)) { self.notArgOnly(in.a); }
            if (!in.bIsImm && !(in.op == IROp.PtrStore && self.storesImmediate(p, fn, in))
                && !(in.op == IROp.Bounds && self.immediateIn(p, fn, in.b))) { self.notArgOnly(in.b); }
            self.notArgOnly(in.x);
            if (in.op != IROp.Call && in.op != IROp.CallIndirect) {
                for k in 0..in.argCount { self.notArgOnly(p.args.get(in.firstArg + k)); }
            }
            for k in 0..in.pieceCount { self.notArgOnly(p.asmVals.get(in.firstPiece + k)); }
        }
    }
    notArgOnly &self t:Temp -> void {
        r: long = t - self.base;
        if (t != NO_TEMP && r >= 0 && r < self.argOnly.len()) { self.argOnly.set(r, false); }
    }

    // Whether a load or store based at `t` (with index `x`) can name `t`'s address in its own
    // addressing mode: `t` is a frame slot's address (`rbp` plus a constant) or, when there is no
    // index, a global's (`rip`-relative, which takes no index register).
    addressInPlace &self p:IRProgram fn:IRFunc t:Temp x:Temp -> bool {
        r: long = t - self.base;
        if (t == NO_TEMP || r < 0 || r >= self.rematKind.len()) { return false; }
        k: long = self.rematKind.get(r);
        if (k == REMAT_AGG) { return true; }
        if (k != REMAT_ADDR) { return false; }
        d: long = fn.firstInstr + self.rematDef.get(r);
        return !p.code[d].isGlobal || x == NO_TEMP;
    }

    // Whether `t` is a constant the sign-extended 32-bit immediate field holds.
    immediateIn &self p:IRProgram fn:IRFunc t:Temp -> bool {
        r: long = t - self.base;
        if (t == NO_TEMP || r < 0 || r >= self.rematKind.len() || self.rematKind.get(r) != REMAT_CONST) { return false; }
        d: long = fn.firstInstr + self.rematDef.get(r);
        v: long = p.code[d].imm;
        return v >= 0 - 2147483648 && v <= 2147483647;
    }

    // Whether store `in` can carry its value as an immediate: an integer constant, which the store
    // writes the low bytes of, and at eight bytes one that fits the sign-extended 32-bit field.
    storesImmediate &self p:IRProgram fn:IRFunc in:Instr -> bool {
        r: long = in.b - self.base;
        if (in.b == NO_TEMP || r < 0 || r >= self.rematKind.len() || self.rematKind.get(r) != REMAT_CONST) { return false; }
        if (isFloatLit(in.kind) || isAggregate(in.kind)) { return false; }
        d: long = fn.firstInstr + self.rematDef.get(r);
        v: long = p.code[d].imm;
        return widthOf(in.kind) < 8 || (v >= 0 - 2147483648 && v <= 2147483647);
    }

    // A value computed only to be compared by the branch right after it (`fusesInto`): `t = a &
    // m` tested against zero, or `t = [p]` compared with something. The emitter writes the
    // comparison where `t` is computed (`test a, m`, `cmp dword [p], b`) and the branch alone
    // where it stands; `t` is never written and gets no register. Only deleted instructions lie
    // between the two, so nothing is emitted between them to change the flags, and every
    // operand the comparison reads is read at the defining instruction, where its range covers
    // it: the branch's other operand is live there too, since it is read just after.
    markFused &self p:IRProgram fn:IRFunc -> void {
        n: long = self.tempReg.len();
        self.fused.clear();
        self.fusedAt.clear();
        for t in 0..n { self.fused.push(false); self.fusedAt.push(-1); }
        for k in 0..self.intervals.len() {
            cur: Interval = self.intervals.get(k);
            s: long = cur.start;
            e: long = cur.end;
            if (e <= s || self.rematDef.get(cur.temp) != s || self.tempReg.get(cur.temp) == REG_RAX) { continue; }
            j: long = s + 1;
            while (j < e && p.code[fn.firstInstr + j].op == IROp.Nop) { j = j + 1; }
            if (j != e) { continue; }
            if (!fusesInto(p, p.code.get(fn.firstInstr + s), p.code.get(fn.firstInstr + e), self.base + cur.temp)) { continue; }
            self.fused.set(cur.temp, true);
            self.fusedAt.set(cur.temp, e);
        }
    }

    isFused &self t:Temp -> bool {
        r: long = t - self.base;
        return t != NO_TEMP && r >= 0 && r < self.fused.len() && self.fused.get(r);
    }
    fusedBranch &self t:Temp -> long { return self.fusedAt.get(t - self.base); }

    // Written once and never read: a call's result nobody wants.
    unread &self t:Temp -> bool {
        r: long = t - self.base;
        return t != NO_TEMP && r >= 0 && r < self.tempReg.len() && self.rematDef.get(r) >= 0
            && self.endOf.get(r) == self.rematDef.get(r);
    }

    // Which floats may live in an `xmm` register: a temp of type `f64`/`f32` whose every definition
    // and use is one the emitter serves from one (`asm.k`: float arithmetic, comparisons and
    // branches, copies, constants, a float's load and store, conversions, a return, a call's
    // result, a named slot's load and store). Anything else (an argument, an `asm` operand, a
    // pointer's place...) keeps it in the general registers, as its bits, where every instruction
    // can read it.
    markXmm &self p:IRProgram fn:IRFunc n:long -> void {
        self.xmmOk.clear();
        for t in 0..n {
            k: Lit = p.kindOf(self.base + t);
            self.xmmOk.push(k == Lit.Float || k == Lit.Double);
        }
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            o: IROp = in.op;
            if (o == IROp.Nop || o == IROp.Label || o == IROp.Jmp) { continue; }
            fl: bool = in.kind == Lit.Float || in.kind == Lit.Double;
            okD: bool = false;
            okA: bool = false;
            okB: bool = false;
            if (fl && (o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.Div || o == IROp.BXor)) {
                okD = true; okA = true; okB = true;
            } else if (fl && (isCompare(o) || o == IROp.Jcc)) { okA = true; okB = true; }
            else if (o == IROp.Mov || o == IROp.Load) { okD = true; okA = o == IROp.Mov; }
            else if (o == IROp.Const) { okD = true; }
            else if (fl && o == IROp.PtrLoad) { okD = true; }
            else if (fl && o == IROp.PtrStore) { okB = true; }
            else if (o == IROp.Store || o == IROp.Ret) { okA = true; }
            else if (o == IROp.Convert) { okA = isFloatLit(in.fromKind); okD = isFloatLit(in.toKind); }
            else if (o == IROp.Call || o == IROp.CallIndirect) { okD = true; }
            if (!okD) { self.noXmm(in.dst); }
            if (!okA) { self.noXmm(in.a); }
            if (!okB && !in.bIsImm) { self.noXmm(in.b); }
            self.noXmm(in.x);
            // A float argument is moved into its `xmm` argument register from wherever it is.
            if (o != IROp.Call && o != IROp.CallIndirect) {
                for k in 0..in.argCount { self.noXmm(p.args.get(in.firstArg + k)); }
            }
            for k in 0..in.pieceCount { self.noXmm(p.asmVals.get(in.firstPiece + k)); }
        }
    }

    // Which temps the emitter may compute again at each read when they get no register. Such a
    // temp has one definition, a `Const`, an `AddrOf`, an `AggSlot` or a `StrLitVal`, and no read
    // that the emitter takes straight from a slot without checking (an `asm` input, a division's
    // operand, a float argument).
    markRemat &self p:IRProgram fn:IRFunc n:long -> void {
        self.rematKind.clear();
        self.rematDef.clear();
        for t in 0..n { self.rematKind.push(REMAT_NONE); self.rematDef.push(-2); }
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            o: IROp = p.code[ix].op;
            if (o == IROp.Nop || o == IROp.Label) { continue; }
            d: long = p.code[ix].dst - self.base;
            if (p.code[ix].dst != NO_TEMP && d >= 0 && d < n) {
                if (self.rematDef.get(d) != -2) { self.rematDef.set(d, -1); }      // a second definition
                else {
                    self.rematDef.set(d, i);
                    k: long = REMAT_NONE;
                    if (o == IROp.Const) { k = REMAT_CONST; }
                    else if (o == IROp.AddrOf && p.code[ix].name != NO_SYM) { k = REMAT_ADDR; }
                    else if (o == IROp.AggSlot) { k = REMAT_AGG; }
                    else if (o == IROp.StrLitVal) { k = REMAT_STR; }
                    self.rematKind.set(d, k);
                }
            }
            if (o == IROp.Div || o == IROp.Mod) {
                self.noRemat(p.code[ix].a);
                if (!p.code[ix].bIsImm) { self.noRemat(p.code[ix].b); }
            }
            if (o == IROp.Asm) {
                in: Instr = p.code.get(ix);
                for k in 0..in.pieceCount { self.noRemat(p.asmVals.get(in.firstPiece + k)); }
            }
            // A float argument goes to its `xmm` register from where it is, with every general
            // register perhaps holding another argument by then.
            if (o == IROp.Call || o == IROp.CallIndirect) {
                in: Instr = p.code.get(ix);
                for k in 0..in.argCount {
                    a: Temp = p.args.get(in.firstArg + k);
                    if (a != NO_TEMP && isFloatLit(p.kindOf(a))) { self.noRemat(a); }
                }
            }
        }
        for t in 0..n { if (self.rematDef.get(t) < 0) { self.rematKind.set(t, REMAT_NONE); } }
    }
    noRemat &self t:Temp -> void {
        r: long = t - self.base;
        if (t != NO_TEMP && r >= 0 && r < self.rematKind.len()) { self.rematKind.set(r, REMAT_NONE); }
    }

    // What computes `t` again when it is spilled (REMAT_NONE: it lives in its slot), and where.
    rematOf &self t:Temp -> long {
        r: long = t - self.base;
        if (r < 0 || r >= self.tempReg.len() || self.tempReg.get(r) != SPILLED) { return REMAT_NONE; }
        return self.rematKind.get(r);
    }
    rematAt &self t:Temp -> long { return self.rematDef.get(t - self.base); }

    // Whether instruction `ix` is a call that may reach code outside the Kiln convention, which
    // need not keep `xmm12` to `xmm14`: a call to a function declared without a body, or one
    // through a pointer (a fn value may hold such a function's address). A call that never
    // returns has nothing after it to keep.
    clobbersXmm &self p:IRProgram ix:long -> bool {
        o: IROp = p.code[ix].op;
        if (o == IROp.CallIndirect) { return self.anyForeign; }
        if (o != IROp.Call || p.code[ix].noReturn) { return false; }
        return self.foreign.has(p.code[ix].name as long);
    }

    noXmm &self t:Temp -> void {
        r: long = t - self.base;
        if (t != NO_TEMP && r >= 0 && r < self.xmmOk.len()) { self.xmmOk.set(r, false); }
    }

    // Every temp live on entry to a `recover` handler (a block a `FaultEdge` names) is kept in the
    // frame (`inFrame`). Each of its writes then lands in its slot before any call after it, so
    // the slot holds the value the handler needs whichever call raised.
    markHandlerLive &self p:IRProgram fn:IRFunc g:CFG n:long -> void {
        if (!fn.holdsRecover) { return; }
        self.inFrame.clear();
        for i in 0..n { self.inFrame.push(false); }
        handlers: HashMap<long, bool>;
        for i in 0..fn.instrCount {
            if (p.code[fn.firstInstr + i].op == IROp.FaultEdge) { handlers.put(p.code[fn.firstInstr + i].name as long, true); }
        }
        if (handlers.len() == 0) { return; }
        for b in 0..g.blocks.len() {
            first: Instr = p.code.get(fn.firstInstr + g.blocks.get(b).start);
            if (first.op != IROp.Label || !handlers.has(first.name as long)) { continue; }
            live: long = g.setBase(b, LIVE_IN);
            for t in 0..n {
                if (g.inSet(live, self.base + t)) { self.inFrame.set(t, true); }
            }
        }
    }

    // A temp's range is the span from the earliest point it is live or defined to the latest point
    // it is live or used. For a value carried around a loop that covers the whole loop, so it can
    // stay in a register across iterations instead of round-tripping through memory.
    computeIntervals &self p:IRProgram fn:IRFunc -> void {
        base: Temp = self.base;
        n: long = fn.tempCount - base;
        if (n < 0) { n = 0; }
        lo: Vec<long>; hi: Vec<long>;
        for i in 0..n { lo.push(-1); hi.push(-1); }
        wt: Vec<long>;
        for i in 0..n { wt.push(0); }
        self.defW.clear();
        for i in 0..n { self.defW.push(0); }
        depthW: Vec<long> = loopWeights(p, fn);

        g: CFG;
        g.build(p, fn);
        g.liveness();
        self.markHandlerLive(p, fn, g, n);

        // Definitions and uses pin the range at the instructions that touch it. Every temp id is
        // shifted into this function's own numbering; one belonging to another function comes out
        // negative and `markRange` drops it.
        for idx in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + idx);
            markRange(&lo, &hi, in.a - base, idx);
            if (!in.bIsImm) { markRange(&lo, &hi, in.b - base, idx); }
            markRange(&lo, &hi, in.x - base, idx);
            for k in 0..in.argCount {
                markRange(&lo, &hi, p.args.get(in.firstArg + k) - base, idx);
            }
            for k in 0..in.pieceCount {
                markRange(&lo, &hi, p.asmVals.get(in.firstPiece + k) - base, idx);
            }
            markRange(&lo, &hi, in.dst - base, idx);
            if (in.op != IROp.Nop) {
                w: long = depthW.get(idx);
                addWeight(&wt, in.a - base, w);
                if (!in.bIsImm) { addWeight(&wt, in.b - base, w); }
                addWeight(&wt, in.x - base, w);
                addWeight(&wt, in.dst - base, w);
                addWeight(&self.defW, in.dst - base, w);
                for k in 0..in.argCount { addWeight(&wt, p.args.get(in.firstArg + k) - base, w); }
            }
        }

        // Liveness then widens it across the blocks the value has to survive: live on entry means
        // live from the block's first instruction, live on exit means live to its last. A
        // loop-carried temp is both, which is what makes it span the back edge. The set bits are
        // read off a word at a time, because asking about every temp in every block costs blocks
        // times temps, which in a function grown by inlining was most of the allocator's time.
        for b in 0..g.blocks.len() {
            bb: BasicBlock = g.blocks.get(b);
            markLive(&lo, &hi, g, g.setBase(b, LIVE_IN), bb.start);
            markLive(&lo, &hi, g, g.setBase(b, LIVE_OUT), bb.end);
        }

        // A range crosses a call, an `asm` block or a `memcpy` when one lies strictly inside it, since
        // each trashes caller-saved registers (`rep movsb` takes rdi, rsi and rcx). A call that never returns does not count: nothing is
        // read after it, so nothing has to survive it. Every bounds check's panic is such a call,
        // and counting them would push each value live across a checked loop into a callee-saved
        // register or a stack slot.
        //
        // So count the register-clobbering instructions before each index; whether a range spans
        // one is then a subtraction rather than a walk over the range.
        clob: Vec<long>;
        c: long = 0;
        for idx in 0..fn.instrCount {
            clob.push(c);
            in: Instr = p.code.get(fn.firstInstr + idx);
            if ((clobbersRegisters(in.op) || in.op == IROp.MemCopy) && !(in.op == IROp.Call && in.noReturn)) { c = c + 1; }
        }
        clob.push(c);
        // The same count for the calls that may not keep `xmm12` to `xmm14` (`clobbersXmm`).
        if (self.foreignN != p.externs.len()) {
            self.foreign.clear();
            for i in 0..p.externs.len() { self.foreign.put(p.externs.get(i) as long, true); }
            self.foreignN = p.externs.len();
        }
        self.anyForeign = p.externs.len() > 0 || gOpenObject || gKlibMode;
        xclob: Vec<long>;
        c = 0;
        for idx in 0..fn.instrCount {
            xclob.push(c);
            if (self.clobbersXmm(p, fn.firstInstr + idx)) { c = c + 1; }
        }
        xclob.push(c);

        self.endOf.clear();
        self.startOf.clear();
        for i in 0..n { self.endOf.push(hi.get(i)); self.startOf.push(lo.get(i)); }
        self.markXmm(p, fn, n);
        self.markRemat(p, fn, n);
        exact: bool = !gExactCallsOff;
        if (exact) { self.liveAcross(p, fn, g, n, depthW); }
        t: Temp = 0;
        while (t < n) {
            if (lo.get(t) >= 0) {
                // A clobber strictly inside (start, end).
                s: long = lo.get(t) + 1;
                e: long = hi.get(t);
                crosses: bool = e > s && clob.get(e) - clob.get(s) > 0;
                foreignCall: bool = e > s && xclob.get(e) - xclob.get(s) > 0;
                if (exact) { crosses = self.across.get(t) != 0; foreignCall = self.xAcross.get(t); }
                self.intervals.push(Interval { temp: t, start: lo.get(t), end: hi.get(t),
                                               crossesCall: crosses, weight: wt.get(t),
                                               xmm: self.xmmOk.get(t) && !foreignCall,
                                               remat: self.rematKind.get(t) != REMAT_NONE });
            }
            t = t + 1;
        }
    }

    // What clobbering instruction `ix` may change. A direct call to a function the emitter has
    // finished changes what that function's text may change (`fnMask`), the registers its
    // arguments are passed in (argument k in register k; a float's counted too, which only adds)
    // and the scratch. A `memcpy` changes rdi, rsi and rcx, which `rep movsb` moves and counts
    // in, and the scratch, which a short copy goes through (`emitMemCopy`). A call through a
    // pointer, one to a function not yet written (one that calls back into its caller, one in
    // another object or another package, one declared without a body) and an `asm` block change
    // every register a callee need not keep.
    siteMask &self p:IRProgram ix:long -> long {
        if (gIpraOff) { return MASK_FULL; }
        if (p.code[ix].op == IROp.MemCopy) { return MASK_SCRATCH | (1 << REG_RDI) | (1 << REG_RSI) | (1 << REG_RCX); }
        if (p.code[ix].op != IROp.Call) { return MASK_FULL; }
        hit: Option<long> = self.fnMask.find(p.code[ix].name as long);
        m: long = MASK_FULL;
        match hit { Some(v) { m = v; } None { return MASK_FULL; } }
        n: long = p.code[ix].argCount;
        if (n > INT_ARG_REGS) { n = INT_ARG_REGS; }
        return m | ((1 << n) - 1) | MASK_SCRATCH;
    }

    // What instruction `i` of this function, a clobbering one, may change (`siteMask`): kept in
    // `crossList` just before the temps live across it.
    siteAt &self i:long -> long {
        f: long = self.crossAt(i);
        if (f < 1) { return MASK_FULL; }
        return self.crossList.get(f - 1);
    }

    // Which temps a clobbering instruction (a call that returns, an `asm` block, a `memcpy`) must
    // keep: live after it and not written by it (`across`), and the same for the calls that may
    // reach foreign code (`xAcross`). A backward walk of each block from what is live out of it.
    liveAcross &self p:IRProgram fn:IRFunc g:CFG n:long depthW:Vec<long> -> void {
        self.across.clear();
        self.xAcross.clear();
        self.crossW.clear();
        for t in 0..n { self.across.push(0); self.xAcross.push(false); self.crossW.push(0); }
        self.crossFirst.clear();
        self.crossCount.clear();
        self.crossList.clear();
        for i in 0..fn.instrCount { self.crossFirst.push(-1); self.crossCount.push(0); }
        live: Vec<long>;
        for w in 0..g.perSet { live.push(0); }
        for b in 0..g.blocks.len() {
            bb: BasicBlock = g.blocks.get(b);
            outAt: long = g.setBase(b, LIVE_OUT);
            for w in 0..g.perSet { live.set(w, g.words.get(outAt + w)); }
            i: long = bb.end;
            while (i >= bb.start) {
                ix: long = fn.firstInstr + i;
                o: IROp = p.code[ix].op;
                if (o != IROp.Nop) {
                    if ((clobbersRegisters(o) || o == IROp.MemCopy) && !(o == IROp.Call && p.code[ix].noReturn)) {
                        xc: bool = self.clobbersXmm(p, ix);
                        d: long = p.code[ix].dst - self.base;
                        cw: long = depthW.get(i);
                        sm: long = self.siteMask(p, ix);
                        self.crossList.push(sm);
                        self.crossFirst.set(i, self.crossList.len());
                        for w in 0..g.perSet {
                            v: long = live.get(w);
                            if (v == 0) { continue; }
                            x: u64 = v as u64;
                            t: long = w * 64;
                            while (x != 0) {
                                if ((x & 1) != 0 && t != d && t < n) {
                                    self.across.set(t, self.across.get(t) | sm);
                                    if (xc) { self.xAcross.set(t, true); }
                                    self.crossList.push(t);
                                    self.crossW.set(t, self.crossW.get(t) + cw);
                                }
                                x = x >> 1;
                                t = t + 1;
                            }
                        }
                        self.crossCount.set(i, self.crossList.len() - self.crossFirst.get(i));
                    }
                    clearBit(&live, p.code[ix].dst - self.base, n);
                    setBit(&live, p.code[ix].a - self.base, n);
                    if (!p.code[ix].bIsImm) { setBit(&live, p.code[ix].b - self.base, n); }
                    setBit(&live, p.code[ix].x - self.base, n);
                    na: long = p.code[ix].argCount;
                    fa: long = p.code[ix].firstArg;
                    for k in 0..na { setBit(&live, p.args.get(fa + k) - self.base, n); }
                    np: long = p.code[ix].pieceCount;
                    fp: long = p.code[ix].firstPiece;
                    for k in 0..np { setBit(&live, p.asmVals.get(fp + k) - self.base, n); }
                }
                i = i - 1;
            }
        }
        self.crossStore.clear();
        for k in 0..self.crossList.len() { self.crossStore.push(true); }
        if (!gSinkHomesOff && self.crossList.len() > 0) { self.changedAt(p, fn, g, n); }
    }

    // Which temps live across a clobbering instruction may have been written since their home
    // last held them (`crossStore`): forward over the blocks to a fixpoint, a temp changed where
    // some path to here writes it after the last such instruction it was live across, which left
    // its home holding it. At the entry everything counts as changed: the parameters arrive in
    // registers.
    changedAt &self p:IRProgram fn:IRFunc g:CFG n:long -> void {
        W: long = g.perSet;
        nb: long = g.blocks.len();
        chIn: Vec<long>;
        for k in 0..nb * W { chIn.push(0); }
        for w in 0..W { chIn.set(w, 0 - 1); }
        cur: Vec<long>;
        for w in 0..W { cur.push(0); }
        going: bool = true;
        rounds: long = 0;
        while (going && rounds < 50) {
            going = false;
            rounds = rounds + 1;
            for b in 0..nb {
                for w in 0..W { cur.set(w, chIn.get(b * W + w)); }
                self.changedWalk(p, fn, g, b, n, &cur, false);
                bb: BasicBlock = g.blocks.get(b);
                for k in 0..bb.succCount {
                    sb: long = g.succs.get(bb.firstSucc + k);
                    for w in 0..W {
                        v: long = chIn.get(sb * W + w) | cur.get(w);
                        if (v != chIn.get(sb * W + w)) { chIn.set(sb * W + w, v); going = true; }
                    }
                }
            }
        }
        for b in 0..nb {
            for w in 0..W { cur.set(w, chIn.get(b * W + w)); }
            self.changedWalk(p, fn, g, b, n, &cur, true);
        }
    }

    // `cur`, what may have changed before block `b`, walked forward through it; with `mark`, each
    // crossing's entry noted as needing its store or not on the way.
    changedWalk &self p:IRProgram fn:IRFunc g:CFG b:long n:long inout cur:Vec<long> mark:bool -> void {
        bb: BasicBlock = g.blocks.get(b);
        for i in bb.start..bb.end + 1 {
            ix: long = fn.firstInstr + i;
            if (p.code[ix].op == IROp.Nop) { continue; }
            f: long = self.crossFirst.get(i);
            if (f >= 0) {
                for k in f..f + self.crossCount.get(i) {
                    t: long = self.crossList.get(k);
                    if (mark) { self.crossStore.set(k, (cur.get(t / 64) & (1 << (t % 64))) != 0); }
                    clearBit(&cur, t, n);
                }
            }
            setBit(&cur, p.code[ix].dst - self.base, n);
        }
    }

    // Insertion sort by start. Intervals arrive nearly ordered (they are produced in temp order,
    // which mostly follows definition order) so this is linear in practice.
    sortByStart &self -> void {
        for i in 1..self.intervals.len() {
            cur: Interval = self.intervals.get(i);
            j: long = i;
            while (j > 0 && self.intervals.get(j - 1).start > cur.start) {
                self.intervals.set(j, self.intervals.get(j - 1));
                j = j - 1;
            }
            self.intervals.set(j, cur);
        }
    }

    // What the range a value hands its register on to is live across. Where `cur` ends at an
    // instruction that may give its result `cur`'s register (`takeOperandReg`, a copy most of
    // all), that result may be live across more calls than `cur` is: a caller-saved register
    // `cur` keeps across its own calls would leave the result to take another, and the copy
    // between them would stay.
    handedOn &self p:IRProgram fn:IRFunc cur:Interval -> long {
        if (!cur.crossesCall || gExactCallsOff || cur.end < 0 || cur.end >= fn.instrCount) { return 0; }
        ix: long = fn.firstInstr + cur.end;
        if (!sharesOperandReg(p.code[ix].op) || p.code[ix].a - self.base != cur.temp) { return 0; }
        d: long = p.code[ix].dst - self.base;
        if (d < 0 || d >= self.startOf.len() || self.startOf.get(d) != cur.end) { return 0; }
        return self.across.get(d);
    }

    // Release the registers of intervals that ended before `at`.
    expireBefore &self at:long -> void {
        i: long = 0;
        while (i < self.active.len()) {
            iv: Interval = self.active.get(i);
            if (iv.end < at) {
                self.freeRegs.set(self.tempReg.get(iv.temp), true);
                self.active.removeAt(i);
            } else {
                i = i + 1;
            }
        }
    }

    // A temp live across calls takes, in this order: a callee-saved register this function already
    // saves; a caller-saved one that none of those calls may change (`survives`), from the last,
    // since a callee takes its own from the first; any callee-saved one; a caller-saved one with a
    // home. Everything else prefers caller-saved, so the callee-saved ones stay available for the
    // temps that genuinely need them.
    // `later`: what the range `cur` hands its register on to may have to keep it across
    // (`handedOn`); a caller-saved register is taken only where that one could keep it too.
    pickRegister &self cur:Interval later:long -> long {
        i: long = 0;
        cm: long = self.clobOf(cur.temp, cur.crossesCall) | later;
        // A float that may live in `xmm` does while one is free: a caller-saved one unless it
        // crosses a call that may change it, else a callee-saved one, and when none is free a
        // general register.
        if (cur.xmm) {
            if (!cur.crossesCall) {
                for x in 0..XMM_CALLER_COUNT { if (self.freeRegs.get(REG_XMM8 + x)) { return REG_XMM8 + x; } }
            } else if ((cm & MASK_CALLER_XMM) != MASK_CALLER_XMM) {
                for x in XMM_CALLER_COUNT..XMM_COUNT {
                    if (self.freeRegs.get(REG_XMM8 + x) && self.usedCallee.get(REG_XMM8 + x)) { return REG_XMM8 + x; }
                }
                x: long = XMM_CALLER_COUNT - 1;
                while (x >= 0) {
                    if (survives(cm, REG_XMM8 + x) && self.freeRegs.get(REG_XMM8 + x)) { return REG_XMM8 + x; }
                    x = x - 1;
                }
            }
            for x in XMM_CALLER_COUNT..XMM_COUNT { if (self.freeRegs.get(REG_XMM8 + x)) { return REG_XMM8 + x; } }
        }
        if (cur.crossesCall) {
            if ((cm & MASK_CALLER_GPR) != MASK_CALLER_GPR) {
                for k in 0..CALLEE_SAVED_COUNT {
                    if (self.freeRegs.get(calleeSavedAt(k)) && self.usedCallee.get(calleeSavedAt(k))) { return calleeSavedAt(k); }
                }
                c: long = CALLER_SAVED_COUNT - 1;
                while (c >= 0) {
                    if (survives(cm, callerSavedAt(c)) && self.freeRegs.get(callerSavedAt(c))) { return callerSavedAt(c); }
                    c = c - 1;
                }
            }
            while (i < CALLEE_SAVED_COUNT) {
                if (self.freeRegs.get(calleeSavedAt(i))) { return calleeSavedAt(i); }
                i = i + 1;
            }
            if (self.homeable(cur)) {
                for c in 0..CALLER_SAVED_COUNT {
                    if (self.freeRegs.get(callerSavedAt(c))) { self.homed.set(cur.temp, true); return callerSavedAt(c); }
                }
            }
            return SPILLED;
        }
        while (i < CALLER_SAVED_COUNT) {
            if (self.freeRegs.get(callerSavedAt(i))) { return callerSavedAt(i); }
            i = i + 1;
        }
        for i in 0..CALLEE_SAVED_COUNT {
            if (self.freeRegs.get(calleeSavedAt(i))) { return calleeSavedAt(i); }
        }
        return SPILLED;
    }

    assign &self cur:Interval reg:long -> void {
        self.tempReg.set(cur.temp, reg);
        self.freeRegs.set(reg, false);
        if (isCalleeSaved(reg)) { self.usedCallee.set(reg, true); }
        // Kept sorted by end, so expiry is a scan from the front.
        at: long = 0;
        while (at < self.active.len() && self.active.get(at).end < cur.end) { at = at + 1; }
        self.active.insert(at, cur);
    }

    // No register is available, so spill whichever of `cur` and the compatible active intervals
    // costs least to keep in memory (the fewest reads and writes, with those inside a loop counted
    // many times over), and among equals the one that ends farthest away, since it would hold a
    // register longest. Choosing by the farthest end alone spilled the counters of a hot inner loop
    // to keep a value that is read once after it in a register.
    spillAround &self cur:Interval -> void {
        steal: long = -1;
        cm: long = self.clobOf(cur.temp, cur.crossesCall);
        for i in 0..self.active.len() {
            r: long = self.tempReg.get(self.active.get(i).temp);
            usable: bool = true;
            if (!survives(cm, r)) { usable = false; }
            if (isXmm(r) && !cur.xmm) { usable = false; }
            if (usable) {
                if (steal < 0 || cheaper(self.active.get(i), self.active.get(steal))) { steal = i; }
            }
        }
        if (steal >= 0 && cheaper(self.active.get(steal), cur)) {
            victim: Interval = self.active.get(steal);
            reg: long = self.tempReg.get(victim.temp);
            self.tempReg.set(victim.temp, SPILLED);
            self.homed.set(victim.temp, false);
            self.active.removeAt(steal);
            self.freeRegs.set(reg, true);
            self.assign(cur, reg);
        } else {
            self.tempReg.set(cur.temp, SPILLED);
        }
    }

    // Whether a temp live across calls is better kept in a caller-saved register with a home in
    // the frame (a store at each write, a load after each call it is live across) than in the
    // frame alone (every read and write a memory access). A temp computed again where it is read
    // costs less in the frame.
    homeable &self cur:Interval -> bool {
        if (gHomesOff || cur.remat || self.crossFirst.len() == 0) { return false; }
        // A call is often made on some turns only (a growth path, an error), where a read is made
        // on every one: a crossing weighs half what a read does.
        return self.defW.get(cur.temp) + self.crossW.get(cur.temp) / 2 <= cur.weight;
    }

    // What a range (of temp `t`, this function's numbering) is live across may change: none for
    // one that crosses nothing, everything with `--no-exact-calls`.
    clobOf &self t:long crossing:bool -> long {
        if (!crossing) { return 0; }
        if (gExactCallsOff) { return MASK_FULL; }
        return self.across.get(t);
    }

    isHomed &self t:Temp -> bool {
        r: long = t - self.base;
        return t != NO_TEMP && r >= 0 && r < self.homed.len() && self.homed.get(r);
    }

    // The temps live across instruction `i` of this function, a clobbering one: a run in
    // `crossList` of this function's own numbering (`crossAt`), `crossN` long.
    crossAt &self i:long -> long {
        if (i < 0 || i >= self.crossFirst.len()) { return -1; }
        return self.crossFirst.get(i);
    }
    crossN &self i:long -> long { return self.crossCount.get(i); }
    crossTemp &self k:long -> Temp { return self.base + self.crossList.get(k); }
    crossStored &self k:long -> bool { return self.crossStore.get(k); }

    // Hold `t` in register `r` while the emitter writes code on terms of its own (the entry
    // guard, `emitGuard`, which reads parameters where they arrive), and put it back after.
    forceReg &self t:Temp r:long -> void {
        x: long = t - self.base;
        if (t != NO_TEMP && x >= 0 && x < self.tempReg.len()) { self.tempReg.set(x, r); }
    }

    // Whether any instruction of this function names `t`: one that none does has no range, no
    // register and no use for a slot.
    hasRange &self t:Temp -> bool {
        r: long = t - self.base;
        return t != NO_TEMP && r >= 0 && r < self.tempReg.len() && self.endOf.get(r) >= 0;
    }

    // Whether `t`'s range starts before instruction `idx`, so its register is its own there.
    liveBefore &self t:Temp idx:long -> bool {
        r: long = t - self.base;
        return t != NO_TEMP && r >= 0 && r < self.startOf.len() && self.startOf.get(r) >= 0 && self.startOf.get(r) < idx;
    }

    // Whether `t`'s whole range lies within instructions `lo..hi`: a value nothing outside them reads.
    rangeWithin &self t:Temp lo:long hi:long -> bool {
        r: long = t - self.base;
        if (t == NO_TEMP || r < 0 || r >= self.startOf.len() || self.startOf.get(r) < 0) { return false; }
        return self.startOf.get(r) >= lo && self.endOf.get(r) <= hi;
    }

    // Whether `t` is still live after instruction `idx` of this function (its range reaches past
    // it). A parameter's temp whose range ends at its own seed is never read.
    liveAfter &self t:Temp idx:long -> bool {
        r: long = t - self.base;
        return t != NO_TEMP && r >= 0 && r < self.tempReg.len() && self.endOf.get(r) > idx;
    }

    // Takes an absolute temp id (what an instruction carries) and translates it into this
    // function's own numbering. A temp from another function is not one of ours, and is SPILLED
    // by the same rule as one this pass could find no register for.
    regOf &self t:Temp -> long {
        r: long = t - self.base;
        if (r < 0 || r >= self.tempReg.len()) { return SPILLED; }
        return self.tempReg.get(r);
    }
}

// The order `secondChance` tries registers in: `xmm` first (taken only by a float that may live
// there), then the caller-saved general ones, then the callee-saved ones.
local choiceAt q:long crossing:bool -> long {
    // Across a call: the callee-saved registers first, then a caller-saved one with a home.
    if (crossing) {
        if (q < XMM_COUNT) { return REG_XMM8 + XMM_COUNT - 1 - q; }
        q1: long = q - XMM_COUNT;
        if (q1 < CALLEE_SAVED_COUNT) { return calleeSavedAt(q1); }
        q4: long = q1 - CALLEE_SAVED_COUNT;
        if (q4 < CALLER_SAVED_COUNT) { return callerSavedAt(q4); }
        return -1;
    }
    if (q < XMM_COUNT) { return REG_XMM8 + q; }
    q2: long = q - XMM_COUNT;
    if (q2 < CALLER_SAVED_COUNT) { return callerSavedAt(q2); }
    q3: long = q2 - CALLER_SAVED_COUNT;
    if (q3 < CALLEE_SAVED_COUNT) { return calleeSavedAt(q3); }
    return -1;
}

// One temp's bit in a set of this function's temps, set or cleared; a temp of another function
// (or none) is no bit at all.
local setBit inout s:Vec<long> r:long n:long -> void {
    if (r < 0 || r >= n) { return; }
    s.set(r / 64, s.get(r / 64) | (1 << (r % 64)));
}
local clearBit inout s:Vec<long> r:long n:long -> void {
    if (r < 0 || r >= n) { return; }
    s.set(r / 64, s.get(r / 64) & ~(1 << (r % 64)));
}

// Widen the range of every temp whose bit is set in the set at `at` to include `idx`.
local markLive inout lo:Vec<long> inout hi:Vec<long> g:CFG at:long idx:long -> void {
    for w in 0..g.perSet {
        v: long = g.words.get(at + w);
        if (v == 0) { continue; }
        x: u64 = v as u64;
        t: long = w * 64;
        while (x != 0) {
            if ((x & 1) != 0) { markRange(lo, hi, t, idx); }
            x = x >> 1;
            t = t + 1;
        }
    }
}

// The instructions whose emitter reads all of its operands before it writes the destination, so
// the destination may share the left operand's register (`takeOperandReg`): each computes in
// `rax`/`rdx`, or in the destination starting from the left operand where it already is.
local sharesOperandReg op:IROp -> bool {
    return op == IROp.Mov || op == IROp.Add || op == IROp.Sub || op == IROp.Mul
        || op == IROp.Div || op == IROp.Mod || op == IROp.BAnd || op == IROp.BOr
        || op == IROp.BXor || op == IROp.Shl || op == IROp.Shr || op == IROp.BNot
        || op == IROp.Convert || op == IROp.PtrLoad || isCompare(op);
}

local isFloatLit k:Lit -> bool { return k == Lit.Float || k == Lit.Double; }

// Whether `w`, defining `t`, can be written as the comparison branch `r` reads it with
// (`markFused`), the flags it leaves being the ones `r` would have tested. Integers only.
// - `t = a & b` tested against zero: `test a, b` sets the flags `and` then `test t, t` set, since
//   the 64-bit `and` of two canonical words is itself canonical (a narrow type's `canonicalize`
//   would change nothing), so both operands must be canonical for the operation's type: of that
//   type, or an immediate that is.
// - `t = [p]` compared with `b`: `cmp <width> [p], b` compares what the load reads at the load's
//   width. At eight bytes that is the word the load gives. Narrower, the load extends it, which
//   keeps order only under the extension's own signedness, so the branch must compare with that
//   signedness, and `b` must be canonical for the load's type for its low bytes to stand for it.
local fusesInto p:IRProgram w:Instr r:Instr t:Temp -> bool {
    if (r.op != IROp.Jcc && r.op != IROp.Jz) { return false; }
    if (r.a != t || isFloatLit(r.kind) || isFloatLit(w.kind) || isAggregate(w.kind)) { return false; }
    if (r.op == IROp.Jcc && !r.bIsImm && (r.b == t || r.b == NO_TEMP)) { return false; }
    k: Lit = w.kind;
    narrow: bool = widthOf(k) < 8;
    if (w.op == IROp.BAnd) {
        if (r.op == IROp.Jcc && !(r.bIsImm && r.bImm == 0)) { return false; }
        if (w.a == NO_TEMP || w.a == t || (!w.bIsImm && (w.b == NO_TEMP || w.b == t))) { return false; }
        if (!narrow) { return true; }
        if (p.kindOf(w.a) != k) { return false; }
        if (w.bIsImm) { return canonicalIn(k, w.bImm); }
        return p.kindOf(w.b) == k;
    }
    // - `t = a / b` or `a % b` compared with anything: the division leaves its result in rax or
    //   rdx as it always does, canonical, and the branch's comparison is made on that register,
    //   the same 64-bit comparison it would have made on `t`'s.
    if (w.op == IROp.Div || w.op == IROp.Mod) { return w.a != t && (w.bIsImm || w.b != t); }
    // - Not a load through an index compared with a constant (a `Jz`'s zero too): `cmp dword
    //   [p + i*4], 0` cannot fuse with its branch, and with an index its load is issued as a
    //   micro-op of its own again, three where `mov` and a `test` fused with the branch are two.
    //   Sieve's test of `sieve[p]` ran 3% slower written that way.
    if (w.op == IROp.PtrLoad) {
        if (w.a == t || w.x == t) { return false; }
        if (w.x != NO_TEMP && (r.op == IROp.Jz || r.bIsImm)) { return false; }
        if (r.op == IROp.Jz) { return true; }
        if (narrow && typeInfo(r.kind).unsignedNum != typeInfo(k).unsignedNum) { return false; }
        if (r.bIsImm) { return !narrow || canonicalIn(k, r.bImm); }
        return !narrow || p.kindOf(r.b) == k;
    }
    return false;
}

// An instruction that may write a value `rax` then holds for the next one (`markRaxPairs`).
local raxWriter in:Instr -> bool {
    o: IROp = in.op;
    if (o == IROp.Call || o == IROp.CallIndirect) { return !in.noReturn; }
    if (isFloatLit(in.kind)) { return false; }
    if (o == IROp.Load) { return !in.paramSeed; }
    if (o == IROp.Convert) { return !isFloatLit(in.fromKind) && !isFloatLit(in.toKind); }
    return o == IROp.Mov || o == IROp.PtrLoad || o == IROp.Add || o == IROp.Sub || o == IROp.Mul
        || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor;
}

// Whether `in` may read `t` from `rax` (`markRaxPairs`), given where it reads it.
local raxReader p:IRProgram in:Instr t:Temp -> bool {
    o: IROp = in.op;
    if (o == IROp.Ret) { return in.a == t && !isFloatLit(in.kind); }
    // The first argument, in no other position, with no argument on the stack: at most as many
    // arguments as the smaller class has registers, whichever class each one is.
    if (o == IROp.Call) {
        if (in.argCount < 1 || in.argCount > FLOAT_ARG_REGS || in.argCount > INT_ARG_REGS) { return false; }
        if (p.args.get(in.firstArg) != t) { return false; }
        for k in 1..in.argCount { if (p.args.get(in.firstArg + k) == t) { return false; } }
        return true;
    }
    if (isFloatLit(in.kind)) { return false; }
    if (o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor) {
        return in.a == t || (!in.bIsImm && in.b == t);
    }
    if (o == IROp.Mov || o == IROp.Store || o == IROp.Jz) { return in.a == t; }
    if (o == IROp.Convert) { return in.a == t && !isFloatLit(in.fromKind) && !isFloatLit(in.toKind); }
    if (o == IROp.Jcc || o == IROp.Bounds) { return in.a == t && (in.bIsImm || in.b != t); }
    if (o == IROp.PtrLoad) { return in.a == t && in.x != t; }
    if (o == IROp.PtrStore) { return in.a == t && in.b != t && in.x != t; }
    return false;
}


// Whether spilling `a` is better than spilling `b`. A value computed again where it is read costs
// an instruction at each read and no store or slot: about half what a spilled value of the same
// weight costs (its reads and its writes), which is what it is weighed at.
local cheaper a:Interval b:Interval -> bool {
    wa: long = a.weight;
    wb: long = b.weight;
    if (a.remat) { wa = wa / 2; }
    if (b.remat) { wb = wb / 2; }
    if (wa != wb) { return wa < wb; }
    if (a.remat != b.remat) { return a.remat; }
    return a.end > b.end;
}

local addWeight inout wt:Vec<long> t:long w:long -> void {
    if (t < 0 || t >= wt.len()) { return; }
    wt.set(t, wt.get(t) + w);
}

// Per instruction, how much a read or write there counts: 1, times 8 per loop around it, up to
// three deep. A loop is a branch back to a label above it; everything between is its body.
local loopWeights p:IRProgram fn:IRFunc -> Vec<long> {
    n: long = fn.instrCount;
    at: HashMap<long, long>;
    // Read in place: the opcode and the name, not a copy of each instruction.
    for i in 0..n {
        if (p.code[fn.firstInstr + i].op == IROp.Label) { at.put(p.code[fn.firstInstr + i].name as long, i); }
    }
    delta: Vec<long>;
    for i in 0..n + 1 { delta.push(0); }
    for i in 0..n {
        if (!isBranch(p.code[fn.firstInstr + i].op)) { continue; }
        hit: Option<long> = at.find(p.code[fn.firstInstr + i].name as long);
        match hit {
            Some(t) {
                if (t <= i) { delta.set(t, delta.get(t) + 1); delta.set(i + 1, delta.get(i + 1) - 1); }
            }
            None { }
        }
    }
    out: Vec<long>;
    d: long = 0;
    for i in 0..n {
        d = d + delta.get(i);
        k: long = d;
        if (k > 3) { k = 3; }
        w: long = 1;
        while (k > 0) { w = w * 8; k = k - 1; }
        out.push(w);
    }
    return out;
}

// Widen [lo, hi] for `t` to include `idx`.
pub markRange inout lo:Vec<long> inout hi:Vec<long> t:Temp idx:long -> void {
    if (t < 0 || t >= lo.len()) { return; }
    if (lo.get(t) < 0 || idx < lo.get(t)) { lo.set(t, idx); }
    if (hi.get(t) < 0 || idx > hi.get(t)) { hi.set(t, idx); }
}
