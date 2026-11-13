// Linear-scan register allocation over one function's temps.
//
// Live ranges come from real liveness over the control-flow graph, so a value can stay in a
// register across a loop's back edge. A range is one span rather than a list of holes:
// conservative, never wrong. A temp live across a call is pinned to a callee-saved register.
#include <{cfg, ir}>
#include <support::compiler>
#include <stdlib::{map, option, vec}>

pub SPILLED: long = -1;

// The physical register numbering the whole back end works in, named here because this is the
// module `asm.k` includes rather than the other way round. `regNames` in asm.k spells these, and
// spells them by index, so the order below and the order it builds are one fact: the indices used
// to be written out again here as bare numbers with a trailing comment naming each one, which
// nothing checked. `checkRegNumbering` in asm.k now does, at build time.
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
// the other six of the first eight plus `r10`/`r11`, and the callee-saved set is `r12`-`r15`.
pub CALLER_SAVED_COUNT: long = 8;
pub CALLEE_SAVED_COUNT: long = 4;

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

pub isCalleeSaved r:long -> bool { return r >= REG_R12 && r <= REG_R15; }

// Floats get a register class of their own: `xmm8`-`xmm14`, numbered after the general registers.
// (`xmm0`-`xmm7` carry float arguments and `xmm0`/`xmm1` are each float operation's scratch,
// `xmm15` a block copy's.) Every `xmm` register is caller-saved here as in System V, so a float
// live across a call takes a callee-saved general register (its bits) or a stack slot, as before.
pub REG_XMM8: long = 14;
pub XMM_COUNT: long = 7;
pub REG_SLOTS: long = 21;      // general and `xmm` registers together, the size of per-register tables
pub isXmm r:long -> bool { return r >= REG_XMM8 && r < REG_SLOTS; }

// One temp's live range, and whether it has to survive a call.
// `weight` is what spilling it would cost: its reads and writes, each counted by how deeply it
// sits in loops.
// `xmm`: the temp is a float whose every use the emitter can serve from an `xmm` register.
pub struct Interval { temp: Temp, start: long, end: long, crossesCall: bool, weight: long, xmm: bool }

pub struct RegAlloc {
    // Indexed by a temp's position within this function: `t - base`. Temps are numbered across
    // the whole program, so indexing this by the temp id gave every function an entry for every
    // temp in the program, all of them SPILLED and every one of them then handed eight bytes of
    // frame by the emitter.
    tempReg: Vec<long>,          // physical register per temp of this function, or SPILLED
    base: Temp,                  // this function's first temp; `Interval.temp` is relative to it
    usedCallee: Vec<bool>,       // which callee-saved registers the prologue must save
    intervals: Vec<Interval>,
    active: Vec<Interval>,       // currently assigned, kept sorted by end ascending
    freeRegs: Vec<bool>,         // indexed by physical register
    endOf: Vec<long>,            // per temp of this function, where its range ends (-1: none)
    xmmOk: Vec<bool>             // per temp: a float every instruction touching it handles in `xmm`
}

methods RegAlloc for Default {
    new -> RegAlloc {
        return RegAlloc { tempReg: vec![], base: 0, usedCallee: vec![], intervals: vec![], active: vec![],
                          freeRegs: vec![], endOf: vec![], xmmOk: vec![] };
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
        self.usedCallee.clear();
        for i in 0..REG_SLOTS { self.usedCallee.push(false); }
        if (n == 0) { return; }

        self.computeIntervals(p, fn);
        self.sortByStart();

        self.freeRegs.clear();
        for i in 0..REG_SLOTS { self.freeRegs.push(false); }
        for i in 0..CALLER_SAVED_COUNT { self.freeRegs.set(callerSavedAt(i), true); }
        for i in 0..XMM_COUNT { self.freeRegs.set(REG_XMM8 + i, true); }
        for i in 0..CALLEE_SAVED_COUNT { self.freeRegs.set(calleeSavedAt(i), true); }

        for k in 0..self.intervals.len() {
            cur: Interval = self.intervals.get(k);
            self.expireBefore(cur.start);
            if (self.takeOperandReg(p, fn, cur)) { continue; }
            reg: long = self.pickRegister(cur);
            if (reg != SPILLED) { self.assign(cur, reg); }
            else { self.spillAround(cur); }
        }
    }

    // `d = op a, ...` where this is the last read of `a`: `d` takes `a`'s register as `a` lets go
    // of it, and the emitter's `mov d, a` before a two-operand instruction disappears. Only for
    // the instructions whose emitter reads every operand before it writes the destination (all of
    // these compute in `rax`/`rdx`, or into the destination from the left operand in place), and
    // only where `d`'s range starts at this definition, so nothing of `d` lives before it.
    takeOperandReg &self p:IRProgram fn:IRFunc cur:Interval -> bool {
        in: Instr = p.code.get(fn.firstInstr + cur.start);
        if (in.dst - self.base != cur.temp || in.a == NO_TEMP || in.a == in.dst) { return false; }
        if (!sharesOperandReg(in.op)) { return false; }
        ra: long = in.a - self.base;
        if (ra < 0 || ra >= self.tempReg.len() || self.endOf.get(ra) != cur.start) { return false; }
        reg: long = self.tempReg.get(ra);
        if (reg == SPILLED || (cur.crossesCall && !isCalleeSaved(reg))) { return false; }
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
            for k in 0..in.argCount { self.noXmm(p.args.get(in.firstArg + k)); }
            for k in 0..in.pieceCount { self.noXmm(p.asmVals.get(in.firstPiece + k)); }
        }
    }

    noXmm &self t:Temp -> void {
        r: long = t - self.base;
        if (t != NO_TEMP && r >= 0 && r < self.xmmOk.len()) { self.xmmOk.set(r, false); }
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
        depthW: Vec<long> = loopWeights(p, fn);

        g: CFG;
        g.build(p, fn);
        g.liveness();

        // Definitions and uses pin the range at the instructions that touch it. Every temp id is
        // shifted into this function's own numbering; one belonging to another function comes out
        // negative and `markRange` drops it.
        for idx in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + idx);
            markRange(&lo, &hi, in.a - base, idx);
            if (!in.bIsImm) { markRange(&lo, &hi, in.b - base, idx); }
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
                addWeight(&wt, in.dst - base, w);
                for k in 0..in.argCount { addWeight(&wt, p.args.get(in.firstArg + k) - base, w); }
            }
        }

        // Liveness then widens it across the blocks the value has to survive: live on entry means
        // live from the block's first instruction, live on exit means live to its last. A
        // loop-carried temp is both, which is what makes it span the back edge. Read off the set
        // bits a word at a time: asking every temp of every block was blocks times temps, which in
        // a function grown by inlining was most of the allocator's time.
        for b in 0..g.blocks.len() {
            bb: BasicBlock = g.blocks.get(b);
            markLive(&lo, &hi, g, g.setBase(b, LIVE_IN), bb.start);
            markLive(&lo, &hi, g, g.setBase(b, LIVE_OUT), bb.end);
        }

        // How many register-clobbering instructions come before each index, so whether a range
        // spans one is a subtraction rather than a walk over the range.
        clob: Vec<long>;
        c: long = 0;
        for idx in 0..fn.instrCount {
            clob.push(c);
            in: Instr = p.code.get(fn.firstInstr + idx);
            if (clobbersRegisters(in.op) && !(in.op == IROp.Call && in.noReturn)) { c = c + 1; }
        }
        clob.push(c);

        self.endOf.clear();
        for i in 0..n { self.endOf.push(hi.get(i)); }
        self.markXmm(p, fn, n);
        t: Temp = 0;
        while (t < n) {
            if (lo.get(t) >= 0) {
                // A clobber strictly inside (start, end).
                s: long = lo.get(t) + 1;
                e: long = hi.get(t);
                crosses: bool = e > s && clob.get(e) - clob.get(s) > 0;
                self.intervals.push(Interval { temp: t, start: lo.get(t), end: hi.get(t),
                                               crossesCall: crosses, weight: wt.get(t),
                                               xmm: self.xmmOk.get(t) && !crosses });
            }
            t = t + 1;
        }
    }

    // A range crosses a call or an asm block when one lies strictly inside it: both trash the
    // caller-saved registers. Except a call that never returns: nothing is read after it, so
    // nothing has to survive it. That is every bounds check's panic, which used to sit inside
    // every checked loop and push each value live across the loop into a callee-saved register or
    // a stack slot.

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

    // A cross-call temp must use a callee-saved register; everything else prefers caller-saved, so
    // the callee-saved ones stay available for the temps that genuinely need them.
    pickRegister &self cur:Interval -> long {
        i: long = 0;
        // A float that may live in `xmm` does, while one is free; then in a general register.
        if (cur.xmm) {
            for x in 0..XMM_COUNT { if (self.freeRegs.get(REG_XMM8 + x)) { return REG_XMM8 + x; } }
        }
        if (cur.crossesCall) {
            while (i < CALLEE_SAVED_COUNT) {
                if (self.freeRegs.get(calleeSavedAt(i))) { return calleeSavedAt(i); }
                i = i + 1;
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

    // No register available: spill whichever of `cur` and the compatible active intervals costs
    // least to keep in memory -- the fewest reads and writes, a loop's counting many times over --
    // and of those, the one that ends farthest away, since it occupies a register for longest.
    // Furthest end alone spilled the counters of a hot inner loop to keep a value read once after
    // it in a register.
    spillAround &self cur:Interval -> void {
        steal: long = -1;
        for i in 0..self.active.len() {
            r: long = self.tempReg.get(self.active.get(i).temp);
            usable: bool = true;
            if (cur.crossesCall && !isCalleeSaved(r)) { usable = false; }
            if (isXmm(r) && !cur.xmm) { usable = false; }
            if (usable) {
                if (steal < 0 || cheaper(self.active.get(i), self.active.get(steal))) { steal = i; }
            }
        }
        if (steal >= 0 && cheaper(self.active.get(steal), cur)) {
            victim: Interval = self.active.get(steal);
            reg: long = self.tempReg.get(victim.temp);
            self.tempReg.set(victim.temp, SPILLED);
            self.active.removeAt(steal);
            self.freeRegs.set(reg, true);
            self.assign(cur, reg);
        } else {
            self.tempReg.set(cur.temp, SPILLED);
        }
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

// Whether spilling `a` is better than spilling `b`.
local cheaper a:Interval b:Interval -> bool {
    if (a.weight != b.weight) { return a.weight < b.weight; }
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
    for i in 0..n {
        in: Instr = p.code.get(fn.firstInstr + i);
        if (in.op == IROp.Label) { at.put(in.name as long, i); }
    }
    delta: Vec<long>;
    for i in 0..n + 1 { delta.push(0); }
    for i in 0..n {
        in: Instr = p.code.get(fn.firstInstr + i);
        if (!isBranch(in.op)) { continue; }
        hit: Option<long> = at.find(in.name as long);
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
