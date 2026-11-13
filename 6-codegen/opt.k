// The IR, improved: one function at a time, over the flat instruction run `IRFunc` names.
//
// Every rewrite is in place, and an unwanted instruction becomes a `Nop` rather than being removed,
// since each `IRFunc` after it names its own run by index. The six passes and the order they have
// to run in are in PORT.md. The gate on all of it is the corpus's output, not its assembly.
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
    slotTemp: HashMap<str, Temp>,
    // Names this function may not promote: their address is taken, they are globals, or an `asm`
    // block spells them.
    pinned: HashMap<str, bool>,
    // Labels some branch names (`dropUnusedLabels`).
    named: HashMap<long, bool>,
    // `copyRound`, per temp of the function: the copy it is (block stamp, source, the source's
    // write count then) and its own write count in the block being walked.
    cpStamp: Vec<long>, cpTo: Vec<long>, cpVer: Vec<long>, vStamp: Vec<long>, vCount: Vec<long>, blkSeq: long,
    afterInline: bool,      // the run over spliced code (main.k sets it)

    // Counters, for `--trace-opt`.
    nPromoted: long, nCopies: long, nImm: long, nFused: long, nJumps: long, nDead: long
}

pub var gTraceOpt: bool = false;

methods Opt for Default {
    new -> Opt {
        return Opt { uses: vec![], defs: vec![], defAt: vec![], base: 0,
                     slotTemp: map![], pinned: map![], named: map![],
                     cpStamp: vec![], cpTo: vec![], cpVer: vec![], vStamp: vec![], vCount: vec![], blkSeq: 0, afterInline: false,
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
        self.dropDeadDefs(p, fn);
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
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            self.noteUse(in.a);
            if (!in.bIsImm) { self.noteUse(in.b); }
            for k in 0..in.argCount { self.noteUse(p.args.get(in.firstArg + k)); }
            for k in 0..in.pieceCount { self.noteUse(p.asmVals.get(in.firstPiece + k)); }
            d: long = in.dst - self.base;
            if (in.dst != NO_TEMP && d >= 0 && d < self.defs.len()) {
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
    // Refused for anything the slot's address could reach: a name whose address is taken, a
    // global, a name an `asm` block spells, and anything that is not a scalar, an aggregate
    // lives in memory by definition and is reached through pointers this pass cannot see.
    promoteLocals &self inout p:IRProgram fn:IRFunc -> void {
        // `clear` walks the whole table, which the largest function so far has grown: a map that
        // big is replaced instead, or every function after it pays for that one.
        if (self.pinned.cap() > 512) { self.pinned = map![]; } else { self.pinned.clear(); }
        if (self.slotTemp.cap() > 512) { self.slotTemp = map![]; } else { self.slotTemp.clear(); }
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            // The address of a slot escapes into a pointer nothing here tracks.
            if (in.op == IROp.AddrOf && in.name != NO_SYM) { self.pinned.put(nameOf(in.name), true); }
            // An array element is reached by index, not by name.
            if (in.op == IROp.ArrLoad || in.op == IROp.ArrStore) {
                if (in.name != NO_SYM) { self.pinned.put(nameOf(in.name), true); }
            }
            // A name spelled inside inline assembly is read as a slot, whatever this pass thinks.
            if (in.op == IROp.Asm) {
                for k in 0..in.pieceCount {
                    nm: Sym = p.asmNames.get(in.firstPiece + k);
                    if (nm != NO_SYM) { self.pinned.put(nameOf(nm), true); }
                }
            }
            if (in.op != IROp.Load && in.op != IROp.Store) { continue; }
            if (in.isGlobal || in.name == NO_SYM) {
                if (in.name != NO_SYM) { self.pinned.put(nameOf(in.name), true); }
                continue;
            }
            // An aggregate's slot is the value; a scalar's slot merely holds one, and so does a
            // backed enum's or a distinct type's (`namedScalar`): an integer, kept in a register
            // like the base it is.
            if ((isAggregate(in.kind) && !namedScalar(in.kind, in.structName)) || in.kind == Lit.Void) {
                self.pinned.put(nameOf(in.name), true);
            }
        }

        // A parameter's seed load is its definition (the value is still in its argument register
        // when the function starts) so promoting the name has to keep that load, not replace it.
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            in: Instr = p.code.get(at);
            if (in.op != IROp.Load && in.op != IROp.Store) { continue; }
            if (in.name == NO_SYM || self.pinned.has(nameOf(in.name))) { continue; }
            // A parameter's seed is not a load of a value the body stored. It is where the
            // argument enters the function, and the prologue counts the leading run of them to
            // know which registers to drain. Rewriting it left `seeds` at zero and no parameter
            // was stored anywhere at all. So the seed stays a `Load`, its own dst becomes the
            // variable's temp, and the emitter fills it from the slot once.
            if (in.paramSeed) {
                if (in.dst == NO_TEMP) { continue; }
                if (self.slotTemp.has(nameOf(in.name))) { continue; }
                self.slotTemp.put(nameOf(in.name), in.dst);
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
                // <var> = a  ->  t = a
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
        hit: Option<Temp> = self.slotTemp.find(nameOf(name));
        match hit { Some(t) { return t; } None { } }
        for k in 0..fn.promoCount {
            if (p.promoName.get(fn.firstPromo + k) == name) {
                t: Temp = p.promoTemp.get(fn.firstPromo + k);
                self.slotTemp.put(nameOf(name), t);
                self.nPromoted = self.nPromoted + 1;
                return t;
            }
        }
        return NO_TEMP;
    }

    // ─── 2. copies ───────────────────────────────────────────────────────────

    // `d = Mov s` where `d` has one definition: every read of `d` reads `s` instead, provided `s`
    // is not written between the copy and the read. Within one basic block only: across a
    // branch the question is which definition reaches, and that is what SSA is for.
    propagateCopies &self inout p:IRProgram fn:IRFunc -> void {
        rounds: long = 0;
        while (rounds < MAX_ROUNDS) {
            self.countUses(p, fn);
            changed: long = self.copyRound(p, fn);
            if (changed == 0) { rounds = MAX_ROUNDS; } else { rounds = rounds + 1; }
        }
    }

    // One forward walk per round: within a block, `d = mov s` (d written once) makes every later
    // read of d a read of s, until s is written again (each temp's writes in the block are
    // counted, and a copy remembers the count its source had). The same rewrites the old
    // per-copy walk to the end of the block made, in one pass rather than one per copy: inlined
    // code makes long blocks with many copies. A call is not a barrier (a temp survives one: the
    // allocator gives it a callee-saved register or a slot); a label or a terminator ends the
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
                // Only a temp with a single definition can stand in for another: with two, which
                // value a later read sees depends on the path taken to it.
                s: long = in.a - self.base;
                if (in.op == IROp.Mov && in.a != NO_TEMP && s >= 0 && s < n && self.defCount(in.dst) == 1) {
                    self.cpStamp.set(d, blk);
                    self.cpTo.set(d, in.a);
                    self.cpVer.set(d, self.versionOf(s, blk));
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
    // two instructions are adjacent: nothing can come between them to observe either.
    coalesceMoves &self inout p:IRProgram fn:IRFunc -> void {
        rounds: long = 0;
        while (rounds < MAX_ROUNDS) {
            self.countUses(p, fn);
            changed: long = 0;
            for i in 1..fn.instrCount {
                at: long = fn.firstInstr + i;
                mv: Instr = p.code.get(at);
                def: Instr = p.code.get(at - 1);
                if (mv.op != IROp.Mov || mv.dst == NO_TEMP || mv.a == NO_TEMP) { continue; }
                if (def.dst != mv.a || !pureResult(def.op) || def.paramSeed) { continue; }
                if (self.useCount(mv.a) != 1 || self.defCount(mv.a) != 1) { continue; }
                def.dst = mv.dst;
                p.code.set(at - 1, def);
                p.code.set(at, instr(IROp.Nop));
                self.nCopies = self.nCopies + 1;
                changed = changed + 1;
            }
            if (changed == 0) { rounds = MAX_ROUNDS; } else { rounds = rounds + 1; }
        }
    }

    // ─── 3. immediates ───────────────────────────────────────────────────────

    // A `Const` read exactly once, as the right operand of something that encodes one, stops
    // being a register: the constant rides on the instruction and the `Const` becomes dead.
    selectImmediates &self inout p:IRProgram fn:IRFunc -> void {
        self.countUses(p, fn);
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            in: Instr = p.code.get(at);
            if (in.bIsImm || in.b == NO_TEMP || !takesImmediate(in.op)) { continue; }
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

    // ─── 4. compare and branch, as one ───────────────────────────────────────

    // `CmpLt t, a, b` immediately followed by `Jz L, t` is a branch on the comparison, spelled in
    // five instructions: the compare, a `setcc`, a widening, and then a second compare against
    // zero. Fused it is one compare and one conditional jump.
    //
    // `Jz` jumps when the value is zero (when the comparison did not hold) so the fused branch
    // carries the negation of it. Only when the comparison sits immediately before the branch and
    // its result is read nowhere else: anything between them could set the flags, and a second
    // reader still needs the 0/1.
    fuseBranches &self inout p:IRProgram fn:IRFunc -> void {
        // The counts `selectImmediates` just took: it changes only how constants are read, never
        // how often a comparison's result is.
        i: long = 0;
        while (i + 1 < fn.instrCount) {
            at: long = fn.firstInstr + i;
            c: Instr = p.code.get(at);
            j: Instr = p.code.get(at + 1);
            i = i + 1;
            if (!isCompare(c.op) || j.op != IROp.Jz) { continue; }
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
            p.code.set(at + 1, fused);
            self.nFused = self.nFused + 1;
        }
    }

    // ─── 5. jumps ────────────────────────────────────────────────────────────

    // A `Jmp` whose target is the next thing in the stream, and everything between a terminator
    // and the next label, which nothing can reach.
    simplifyJumps &self inout p:IRProgram fn:IRFunc -> void {
        i: long = 0;
        while (i < fn.instrCount) {
            at: long = fn.firstInstr + i;
            in: Instr = p.code.get(at);
            i = i + 1;
            if (in.op == IROp.Jmp) {
                if (self.nextLabelIs(p, fn, i, in.name)) {
                    p.code.set(at, instr(IROp.Nop));
                    self.nJumps = self.nJumps + 1;
                }
                continue;
            }
            // Only an unconditional exit ends the stream. `isTerminator` says yes to `Jz` and
            // `Jcc` too, and control falls through both when the condition does not hold: using
            // it here deleted every loop body, which is what the fused branch turns the top of a
            // `while` into.
            if (!endsFlow(in.op) && !(in.op == IROp.Call && in.noReturn)) { continue; }
            // Unreachable until a label gives the stream a way back in.
            k: long = i;
            while (k < fn.instrCount) {
                nx: Instr = p.code.get(fn.firstInstr + k);
                if (nx.op == IROp.Label) { k = fn.instrCount; continue; }
                if (nx.op != IROp.Nop) {
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
            if (isBranch(o) && p.code[fn.firstInstr + i].name != NO_SYM) { self.named.put(p.code[fn.firstInstr + i].name as long, true); }
        }
        for i in 0..fn.instrCount {
            at: long = fn.firstInstr + i;
            if (p.code[at].op != IROp.Label || self.named.has(p.code[at].name as long)) { continue; }
            p.code.set(at, instr(IROp.Nop));
            self.nJumps = self.nJumps + 1;
        }
    }

    // Whether the next real instruction from `i` is the label `name`.
    nextLabelIs &self inout p:IRProgram fn:IRFunc i:long name:Sym -> bool {
        for k in i..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Nop) { continue; }
            if (in.op != IROp.Label) { return false; }
            if (in.name == name) { return true; }
            // A run of labels: any of them being the target still means the jump goes nowhere.
        }
        return false;
    }

    // ─── 6. results nobody reads ─────────────────────────────────────────────

    // An instruction whose destination is never read and which does nothing else. A call is not
    // one of these however unused its result: it is what the program was for.
    dropDeadDefs &self inout p:IRProgram fn:IRFunc -> void {
        rounds: long = 0;
        while (rounds < MAX_ROUNDS) {
            self.countUses(p, fn);
            changed: long = 0;
            for i in 0..fn.instrCount {
                at: long = fn.firstInstr + i;
                in: Instr = p.code.get(at);
                if (!pureResult(in.op) || in.dst == NO_TEMP) { continue; }
                if (self.useCount(in.dst) != 0) { continue; }
                // A promoted parameter's seed holds a register; deleting it frees the allocator
                // to put something else there before the value has been read.
                if (in.paramSeed) { continue; }
                p.code.set(at, instr(IROp.Nop));
                self.nDead = self.nDead + 1;
                changed = changed + 1;
            }
            if (changed == 0) { rounds = MAX_ROUNDS; } else { rounds = rounds + 1; }
        }
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
pub takesImmediate op:IROp -> bool {
    return op == IROp.Add || op == IROp.Sub || op == IROp.Mul
        || op == IROp.BAnd || op == IROp.BOr || op == IROp.BXor
        || op == IROp.Shl || op == IROp.Shr
        // A fused compare-and-branch encodes one too. Left out while nothing produced a `Jcc`
        // except this file, `while (i < 1000000)` came out as a constant moved into a register
        // and then compared, which is the shape immediates exist to remove.
        || op == IROp.Jcc
        || isCompare(op);
}

// Whether an instruction's whole effect is its destination, so removing it when nothing reads
// that removes nothing else. A load from a name is one: the slot is still there afterwards.
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
