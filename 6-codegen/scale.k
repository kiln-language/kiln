// Scaled addressing: an element access as one x86 addressing mode.
//
// `p[i]` lowers to `s = i * 8` (a shift once `flow.k` has strength-reduced it), `t = p + s`, then
// `[t + d]`: three instructions and two temps where the machine reads `[p + i*8 + d]` in one. This
// pass puts the base, the index and the scale on the access itself (`Instr.x`, `Instr.scale`) and
// deletes the sum and the shift once nothing else reads them.
//
// It runs after `Flow`, and after a package build has taken the effect summaries it exports, so
// only the allocator and the emitter ever see an index: every analysis before them reads an
// address as one temp. It works within a block only. The sum and the shift must each be their
// temp's one definition, made earlier in the same block, and the base and the index must not be
// written between the point where the sum and the shift read them and the access, since the
// access now reads them itself.
#include <ir>
#include <support::compiler>
#include <stdlib::{option, vec}>

pub var gScaleOff: bool = false;    // `--no-scale`
pub var gScaleConvertOff: bool = false;   // `--no-scale-convert`: no fold through a conversion between word kinds
pub var gScaled: long = 0;          // accesses given an index, for `--trace-opt`
pub var gLeaOff: bool = false;      // `--no-lea`: no sum made one `lea` (`foldArith`)
pub var gLeas: long = 0;            // sums made one `lea`, for `--trace-opt`

pub struct Scaler {
    first: long, n: long, base: Temp, nt: long,
    defs: Vec<long>,        // per temp: how many instructions write it
    defAt: Vec<long>,       // the one that does (relative index)
    reads: Vec<long>,       // how many operands read it
    stamp: Vec<long>,       // the block it was last written in, and where
    pos: Vec<long>,
    addr: Vec<bool>         // read as the address of an access that may fold it (`fold`)
}

methods Scaler for Default {
    new -> Scaler {
        return Scaler { first: 0, n: 0, base: 0, nt: 0, defs: vec![], defAt: vec![], reads: vec![],
                        stamp: vec![], pos: vec![], addr: vec![] };
    }
}

methods Scaler {
    run &self inout p:IRProgram -> void {
        if (gScaleOff) { return; }
        for f in 0..p.funcs.len() { self.runOne(p, p.funcs.get(f)); }
    }

    rel &self t:Temp -> long {
        if (t == NO_TEMP) { return -1; }
        r: long = t - self.base;
        if (r < 0 || r >= self.nt) { return -1; }
        return r;
    }

    addRead &self t:Temp d:long -> void {
        r: long = self.rel(t);
        if (r >= 0) { self.reads.set(r, self.reads.get(r) + d); }
    }

    runOne &self inout p:IRProgram fn:IRFunc -> void {
        if (fn.instrCount == 0) { return; }
        self.first = fn.firstInstr;
        self.n = fn.instrCount;
        self.base = fn.firstTemp;
        self.nt = fn.tempCount - fn.firstTemp;
        if (self.nt <= 0) { return; }
        fill(&self.defs, self.nt, 0);
        fill(&self.defAt, self.nt, -1);
        fill(&self.reads, self.nt, 0);
        fill(&self.stamp, self.nt, 0);
        fill(&self.pos, self.nt, -1);
        self.addr.clear();
        for i in 0..self.nt { self.addr.push(false); }
        for i in 0..self.n {
            in: Instr = p.code.get(self.first + i);
            r: long = self.rel(in.dst);
            if (r >= 0) { self.defs.set(r, self.defs.get(r) + 1); self.defAt.set(r, i); }
            if ((in.op == IROp.PtrLoad || in.op == IROp.PtrStore) && in.x == NO_TEMP) {
                ra: long = self.rel(in.a);
                if (ra >= 0) { self.addr.set(ra, true); }
            }
            self.addRead(in.a, 1);
            if (!in.bIsImm) { self.addRead(in.b, 1); }
            for k in 0..in.argCount { self.addRead(p.args.get(in.firstArg + k), 1); }
            for k in 0..in.pieceCount { self.addRead(p.asmVals.get(in.firstPiece + k), 1); }
        }
        // An access may reach its sum through a conversion between the kinds an address travels
        // as (`(p + i) as *u64`), which `fold` looks through: that sum is an address too.
        if (!gScaleConvertOff) {
            for i in 0..self.n {
                in: Instr = p.code.get(self.first + i);
                if (in.op != IROp.Convert || !isWord(in.fromKind) || !isWord(in.toKind)) { continue; }
                rd: long = self.rel(in.dst);
                ra: long = self.rel(in.a);
                if (rd >= 0 && ra >= 0 && self.addr.get(rd)) { self.addr.set(ra, true); }
            }
        }
        blk: long = 1;
        for i in 0..self.n {
            at: long = self.first + i;
            op: IROp = p.code[at].op;
            if (op == IROp.Label) { blk = blk + 1; continue; }
            if ((op == IROp.PtrLoad || op == IROp.PtrStore) && p.code[at].x == NO_TEMP) { self.fold(p, at, blk); }
            else if ((op == IROp.Add || op == IROp.Sub) && !gLeaOff) { self.foldArith(p, at, blk); }
            r: long = self.rel(p.code[at].dst);
            if (r >= 0) { self.stamp.set(r, blk); self.pos.set(r, i); }
        }
    }

    // Whether `t` is written in this block after relative index `after`. If it is, a read moved
    // from there to here would see another value.
    writtenSince &self t:Temp blk:long after:long -> bool {
        r: long = self.rel(t);
        return r >= 0 && self.stamp.get(r) == blk && self.pos.get(r) > after;
    }

    // `t`'s one definition, made earlier in this block, or -1.
    localDef &self t:Temp blk:long -> long {
        r: long = self.rel(t);
        if (r < 0 || self.defs.get(r) != 1 || self.stamp.get(r) != blk) { return -1; }
        return self.defAt.get(r);
    }

    // The scale an operand of the sum carries, or 0: `i << k` or `i * 2^k` for k from 1 to 3,
    // where the index is the instruction's own operand. Only a full-width shift or multiply
    // counts. An `int` shift wraps at 32 bits (`(1 << 30) << 2` is 0) and the bounds check reads
    // the wrapped value, so `[p + i*4]` would reach memory the check never passed.
    scaleOf &self inout p:IRProgram at:long -> long {
        d: Instr = p.code.get(self.first + at);
        if (d.a == NO_TEMP || !d.bIsImm || !isWord(d.kind)) { return 0; }
        if (d.op == IROp.Shl && d.bImm >= 1 && d.bImm <= 3) { return 1 << d.bImm; }
        if (d.op == IROp.Mul && (d.bImm == 2 || d.bImm == 4 || d.bImm == 8)) { return d.bImm; }
        return 0;
    }

    fold &self inout p:IRProgram at:long blk:long -> void {
        in: Instr = p.code.get(at);
        // Through a conversion between the kinds an address travels as, `(p + i) as *u64` in
        // `unsafe` code: the access reads what was converted, and the conversion goes.
        cv: long = self.localDef(in.a, blk);
        if (!gScaleConvertOff && cv >= 0 && self.reads.get(self.rel(in.a)) == 1) {
            c: Instr = p.code.get(self.first + cv);
            if (c.op == IROp.Convert && c.a != NO_TEMP && isWord(c.fromKind) && isWord(c.toKind)
                && !self.writtenSince(c.a, blk, cv)) {
                self.addRead(in.a, -1);
                in.a = c.a;
                p.code.set(at, in);
                p.code.set(self.first + cv, instr(IROp.Nop));
            }
        }
        sa: long = self.localDef(in.a, blk);
        if (sa < 0) { return; }
        // The sum can only be deleted when every read of it is an access that folds it. If any
        // other reader is left, the sum stays, and the rule below would make the base and the
        // index live longer for nothing. So only a sum with a single reader is folded, which also
        // leaves a store of an element's own address into it (`[t] <- t`) as it is.
        if (self.reads.get(self.rel(in.a)) != 1) { return; }
        sum: Instr = p.code.get(self.first + sa);
        if (sum.op != IROp.Add || sum.bIsImm || sum.a == NO_TEMP || sum.b == NO_TEMP) { return; }
        // The address is a 64-bit sum; one that wraps narrower is not what the access would add.
        if (!isWord(sum.kind)) { return; }
        // Which side is scaled: the right one as the lowerer writes it, else the left.
        baseT: Temp = sum.a;
        idxT: Temp = sum.b;
        scale: long = 1;
        sh: long = -1;
        shT: Temp = NO_TEMP;
        // A shift shared by several accesses (`v[j] = v[j] + w[j]`) is read by each of their sums,
        // and it is deleted once the last of them is folded.
        for side in 0..2 {
            o: Temp = sum.b;
            other: Temp = sum.a;
            if (side == 1) { o = sum.a; other = sum.b; }
            ds: long = self.localDef(o, blk);
            if (ds < 0) { continue; }
            k: long = self.scaleOf(p, ds);
            if (k == 0) { continue; }
            iv: Temp = p.code.get(self.first + ds).a;
            if (self.writtenSince(iv, blk, ds)) { continue; }
            baseT = other; idxT = iv; scale = k; sh = ds; shT = o;
            break;
        }
        if (self.writtenSince(baseT, blk, sa) || self.writtenSince(idxT, blk, sa)) { return; }
        in.a = baseT;
        in.x = idxT;
        in.scale = scale;
        p.code.set(at, in);
        gScaled = gScaled + 1;
        // The sum is read by nothing now, and the shift may not be.
        self.addRead(sum.a, -1);
        self.addRead(sum.b, -1);
        p.code.set(self.first + sa, instr(IROp.Nop));
        if (sh >= 0 && self.reads.get(self.rel(shT)) == 0) {
            self.addRead(idxT, -1);
            p.code.set(self.first + sh, instr(IROp.Nop));
        }
        self.addRead(baseT, 1);
        self.addRead(idxT, 1);
    }

    // A sum the machine computes in one `lea`, made one (`IROp.Lea`): `t = x * 3; u = t + 1` is
    // `lea u, [x + x*2 + 1]`, where it was one `lea` for the product and another for the sum, the
    // second waiting for the first. Into `u = t + c` (or `- c`) folds a product by 3, 5 or 9, a
    // scale (`x << k`, `x * 2^k`, k up to 3), a sum of two values, or a `lea` made before; into
    // `u = y + t`, a scale or `t = x + c`. As for an access, `t` must be its temp's one definition,
    // made earlier in this block and read by `u` alone, and what it read must not have been
    // written since. A word-wide integer only, which is what `lea` adds; and not a sum an access
    // reads as its address, which `fold` makes part of that access instead.
    foldArith &self inout p:IRProgram at:long blk:long -> void {
        u: Instr = p.code.get(at);
        if (!isWord(u.kind) || u.dst == NO_TEMP || u.a == NO_TEMP) { return; }
        ru: long = self.rel(u.dst);
        if (ru >= 0 && self.addr.get(ru)) { return; }
        if (u.op == IROp.Sub && !u.bIsImm) { return; }
        base: Temp = NO_TEMP;
        idx: Temp = NO_TEMP;
        scale: long = 1;
        disp: long = 0;
        d: long = -1;
        if (u.bIsImm) {
            if (u.bImm < 0 - 2147483647 || u.bImm > 2147483647) { return; }
            disp = u.bImm;
            if (u.op == IROp.Sub) { disp = 0 - disp; }
            d = self.localDef(u.a, blk);
            if (d < 0 || self.reads.get(self.rel(u.a)) != 1) { return; }
            td: Instr = p.code.get(self.first + d);
            if (!isWord(td.kind) || td.a == NO_TEMP) { return; }
            k: long = self.scaleOf(p, d);
            if (td.op == IROp.Mul && td.bIsImm && (td.bImm == 3 || td.bImm == 5 || td.bImm == 9)) {
                base = td.a; idx = td.a; scale = td.bImm - 1;
            } else if (k != 0) {
                idx = td.a; scale = k;
            } else if (td.op == IROp.Add && !td.bIsImm && td.b != NO_TEMP) {
                base = td.a; idx = td.b;
            } else if (td.op == IROp.Lea) {
                base = td.a; idx = td.x; scale = td.scale; disp = disp + td.imm;
            } else {
                return;
            }
        } else {
            if (u.op != IROp.Add || u.b == NO_TEMP || u.a == u.b) { return; }
            for side in 0..2 {
                o: Temp = u.b;
                other: Temp = u.a;
                if (side == 1) { o = u.a; other = u.b; }
                ds: long = self.localDef(o, blk);
                if (ds < 0 || self.reads.get(self.rel(o)) != 1) { continue; }
                td: Instr = p.code.get(self.first + ds);
                if (!isWord(td.kind) || td.a == NO_TEMP) { continue; }
                k: long = self.scaleOf(p, ds);
                if (k != 0) {
                    base = other; idx = td.a; scale = k; d = ds;
                    break;
                }
                if ((td.op == IROp.Add || td.op == IROp.Sub) && td.bIsImm
                    && td.bImm >= 0 - 2147483647 && td.bImm <= 2147483647) {
                    base = other; idx = td.a; disp = td.bImm;
                    if (td.op == IROp.Sub) { disp = 0 - disp; }
                    d = ds;
                    break;
                }
            }
            if (d < 0) { return; }
        }
        // `lea` carries a signed 32-bit displacement.
        if (disp < 0 - 2147483647 || disp > 2147483647) { return; }
        if ((base != NO_TEMP && self.writtenSince(base, blk, d)) || self.writtenSince(idx, blk, d)) { return; }
        td: Instr = p.code.get(self.first + d);
        self.addRead(td.a, -1);
        if (!td.bIsImm) { self.addRead(td.b, -1); }
        if (td.op == IROp.Lea) { self.addRead(td.x, -1); }
        self.addRead(u.a, -1);
        if (!u.bIsImm) { self.addRead(u.b, -1); }
        p.code.set(self.first + d, instr(IROp.Nop));
        lea: Instr = instr(IROp.Lea);
        lea.dst = u.dst;
        lea.kind = u.kind;
        lea.a = base;
        lea.x = idx;
        lea.scale = scale;
        lea.imm = disp;
        p.code.set(at, lea);
        self.addRead(base, 1);
        self.addRead(idx, 1);
        gLeas = gLeas + 1;
    }
}

// A 64-bit integer: arithmetic in one wraps exactly as an address does.
local isWord k:Lit -> bool { return k == Lit.Long || k == Lit.U64 || k == Lit.Ptr; }

local fill inout v:Vec<long> n:long x:long -> void {
    v.clear();
    for i in 0..n { v.push(x); }
}
