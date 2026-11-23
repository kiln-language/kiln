// Basic blocks and liveness over one function's IR.
//
// A temp's live range has to come from where its value is needed, not from linear instruction
// order, which cannot describe a value held across a loop's back edge. The dataflow is the
// textbook one iterated to a fixpoint, with the four sets per block packed into one bitset array.
#include <ir>
#include <support::compiler>
#include <stdlib::{map, option, vec}>

pub WORD_BITS: long = 64;

// A block's four sets sit at four consecutive strides in the CFG's word array.
pub USE_SET: long = 0;
pub DEF_SET: long = 1;
pub LIVE_IN: long = 2;
pub LIVE_OUT: long = 3;
pub SETS_PER_BLOCK: long = 4;

pub struct BasicBlock {
    start: long, end: long,              // inclusive instruction range
    firstSucc: long, succCount: long,
    setsAt: long                         // where this block's four sets begin
}

pub struct CFG {
    blocks: Vec<BasicBlock>,
    succs:  Vec<long>,                   // every block's successors, as a run
    words:  Vec<long>,                   // every block's four bitsets, back to back
    perSet: long,                        // words in one set
    // Temps are numbered across the whole program, and a set covers only this function's range of
    // them: bit `t - base` is temp `t`, and `span` is how many bits a set really has. Sized to the
    // program's whole temp count instead, one set ran to some seventeen hundred words for every
    // block of every function, and the liveness fixpoint paid for all of them on every round.
    base:   Temp,
    span:   long,
    labelAt: HashMap<long, long>         // a label's name -> the block it starts
}

methods CFG for Default {
    new -> CFG {
        return CFG { blocks: vec![], succs: vec![], words: vec![], perSet: 0, base: 0, span: 0, labelAt: map![] };
    }
}

methods CFG {
    // ─── bitsets ─────────────────────────────────────────────────────────────

    setBase &self b:long which:long -> long {
        return self.blocks.get(b).setsAt + which * self.perSet;
    }
    // Which bit in a set stands for temp `t`, or -1 when `t` belongs to another function. The
    // range test is against the set, not against the whole word array: a bit past the end of one
    // set is a bit inside the next one, and setting it would make a block's `def` a lie.
    bitOf &self t:Temp -> long {
        r: long = t - self.base;
        if (r < 0 || r >= self.span) { return -1; }
        return r;
    }
    addTo &self base:long t:Temp -> void {
        r: long = self.bitOf(t);
        if (r < 0) { return; }
        w: long = base + r / WORD_BITS;
        if (w >= self.words.len()) { return; }
        self.words.set(w, self.words.get(w) | (1 << (r % WORD_BITS)));
    }
    inSet &self base:long t:Temp -> bool {
        r: long = self.bitOf(t);
        if (r < 0) { return false; }
        w: long = base + r / WORD_BITS;
        if (w >= self.words.len()) { return false; }
        return (self.words.get(w) & (1 << (r % WORD_BITS))) != 0;
    }
    // Union `src` into `dst`. Answers whether anything changed, which is what drives the fixpoint.
    unionInto &self dst:long src:long -> bool {
        changed: bool = false;
        for i in 0..self.perSet {
            was: long = self.words.get(dst + i);
            now: long = was | self.words.get(src + i);
            if (now != was) { self.words.set(dst + i, now); changed = true; }
        }
        return changed;
    }
    // Union `src` into `dst`, skipping anything in `except`.
    unionExcept &self dst:long src:long except:long -> bool {
        changed: bool = false;
        for i in 0..self.perSet {
            was: long = self.words.get(dst + i);
            now: long = was | (self.words.get(src + i) & ~self.words.get(except + i));
            if (now != was) { self.words.set(dst + i, now); changed = true; }
        }
        return changed;
    }

    // ─── building ────────────────────────────────────────────────────────────

    // Split `fn` into blocks, wire the successors, and compute per-block use/def.
    build &self p:IRProgram fn:IRFunc -> void {
        n: long = fn.instrCount;
        if (n == 0) { return; }
        self.base = fn.firstTemp;
        self.span = fn.tempCount - fn.firstTemp;
        if (self.span < 0) { self.span = 0; }
        self.perSet = (self.span + WORD_BITS - 1) / WORD_BITS;
        if (self.perSet < 1) { self.perSet = 1; }

        // Leaders: the first instruction, every label, and whatever follows a transfer.
        leader: Vec<bool>;
        for i in 0..n { leader.push(false); }
        leader.set(0, true);
        i: long = 0;
        while (i < n) {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (in.op == IROp.Label) { leader.set(i, true); }
            if ((isTerminator(in.op) || (in.op == IROp.Call && in.noReturn)) && i + 1 < n) { leader.set(i + 1, true); }
            i = i + 1;
        }

        starts: Vec<long>;
        for i in 0..n {
            if (leader.get(i)) { starts.push(i); }
        }

        for b in 0..starts.len() {
            s: long = starts.get(b);
            e: long = n - 1;
            if (b + 1 < starts.len()) { e = starts.get(b + 1) - 1; }
            first: Instr = p.code.get(fn.firstInstr + s);
            if (first.op == IROp.Label) { self.labelAt.put(first.name as long, b); }
            at: long = self.words.len();
            for k in 0..SETS_PER_BLOCK * self.perSet { self.words.push(0); }
            self.blocks.push(BasicBlock { start: s, end: e, firstSucc: 0, succCount: 0,
                                          setsAt: at });
        }

        self.wireSuccessors(p, fn);
        self.computeUseDef(p, fn);
    }

    wireSuccessors &self p:IRProgram fn:IRFunc -> void {
        b: long = 0;
        while (b < self.blocks.len()) {
            bb: BasicBlock = self.blocks.get(b);
            last: Instr = p.code.get(fn.firstInstr + bb.end);
            mine: Vec<long>;

            fallsThrough: bool = true;
            // A fault edge goes on to the next instruction and, should the call before it raise,
            // to its `recover` handler.
            if (isBranch(last.op) || last.op == IROp.FaultEdge) {
                target: long = self.blockAtLabel(p, fn, last.name);
                if (target >= 0) { mine.push(target); }
                if (last.op == IROp.Jmp) { fallsThrough = false; }
            } else if (last.op == IROp.Ret || last.op == IROp.RetVoid || (last.op == IROp.Call && last.noReturn)) {
                fallsThrough = false;
            }
            if (fallsThrough && b + 1 < self.blocks.len()) { mine.push(b + 1); }

            first: long = self.succs.len();
            self.succs.extend(mine);
            bb.firstSucc = first;
            bb.succCount = mine.len();
            self.blocks.set(b, bb);
            b = b + 1;
        }
    }

    // Which block a label starts. Looked up: a function grown by inlining has thousands of
    // blocks, and a walk over them per branch was quadratic in them.
    blockAtLabel &self p:IRProgram fn:IRFunc name:Sym -> long {
        hit: Option<long> = self.labelAt.find(name as long);
        match hit { Some(b) { return b; } None { } }
        return -1;
    }

    // `use` is read-before-written in this block; `def` is written here. Order matters: a temp
    // written earlier in the block and read later is not a use of anything outside it.
    computeUseDef &self p:IRProgram fn:IRFunc -> void {
        for b in 0..self.blocks.len() {
            bb: BasicBlock = self.blocks.get(b);
            useAt: long = self.setBase(b, USE_SET);
            defAt: long = self.setBase(b, DEF_SET);
            i: long = bb.start;
            while (i <= bb.end) {
                in: Instr = p.code.get(fn.firstInstr + i);
                if (in.a != NO_TEMP && !self.inSet(defAt, in.a)) { self.addTo(useAt, in.a); }
                if (!in.bIsImm && in.b != NO_TEMP && !self.inSet(defAt, in.b)) {
                    self.addTo(useAt, in.b);
                }
                if (in.x != NO_TEMP && !self.inSet(defAt, in.x)) { self.addTo(useAt, in.x); }
                for k in 0..in.argCount {
                    arg: Temp = p.args.get(in.firstArg + k);
                    if (arg != NO_TEMP && !self.inSet(defAt, arg)) { self.addTo(useAt, arg); }
                }
                // An asm block's inputs are reads too: a temp feeding one must survive to it.
                for k in 0..in.pieceCount {
                    v: Temp = p.asmVals.get(in.firstPiece + k);
                    if (v != NO_TEMP && !self.inSet(defAt, v)) { self.addTo(useAt, v); }
                }
                if (in.dst != NO_TEMP) { self.addTo(defAt, in.dst); }
                i = i + 1;
            }
        }
    }

    // Iterate to a fixpoint, backwards over the blocks, which converges fastest for a forward
    // instruction order, since a block's successors usually come after it.
    liveness &self -> void {
        going: bool = true;
        while (going) {
            going = false;
            b: long = self.blocks.len();
            while (b > 0) {
                b = b - 1;
                bb: BasicBlock = self.blocks.get(b);
                outAt: long = self.setBase(b, LIVE_OUT);
                inAt:  long = self.setBase(b, LIVE_IN);
                for k in 0..bb.succCount {
                    s: long = self.succs.get(bb.firstSucc + k);
                    if (self.unionInto(outAt, self.setBase(s, LIVE_IN))) { going = true; }
                }
                if (self.unionInto(inAt, self.setBase(b, USE_SET))) { going = true; }
                if (self.unionExcept(inAt, outAt, self.setBase(b, DEF_SET))) { going = true; }
            }
        }
    }

    // Is `t` live on the way out of block `b`?
    liveOutHas &self b:long t:Temp -> bool { return self.inSet(self.setBase(b, LIVE_OUT), t); }

    // Which block an instruction index falls in.
    blockOf &self i:long -> long {
        for b in 0..self.blocks.len() {
            bb: BasicBlock = self.blocks.get(b);
            if (i >= bb.start && i <= bb.end) { return b; }
        }
        return -1;
    }
}
