// The tree to the IR, one pass per function.
//
// Expressions lower to a temp holding the value, statements to instructions that read and write
// named variable slots. Control flow becomes labels and jumps, numbered per function so that two
// functions never share one.
#include <ir>
#include <parse::{ast, registry, types, upstream}>
#include <transform::{check, eval, facts}>
#include <support::{compiler, fp}>
#include <stdlib::{fmt, chars, string, vec}>

// A function whose last parameter is `...T`: how many parameters come before it (a method's
// receiver counts as one of them) and what T is. A call packs its trailing arguments into the
// slice that parameter reads, so the call site needs this before it lowers the arguments.
pub struct VarSig { fixed: long, elemKind: Lit, elemStruct: Sym }

pub struct Lowerer {
    ir: IRProgram,
    labels: long,          // per-function label counter
    breakTo: Vec<Sym>,     // the label a `break` jumps to, innermost last
    continueTo: Vec<Sym>,

    // Parameters that arrive as a pointer rather than a value. An aggregate is too big for a
    // register, so the caller passes its address and the callee reads through it, which means
    // the address of such a name is the slot's contents, not the slot. Asked once per variable
    // reference, so it is a set and not a list to walk.
    byRef: HashMap<str, long>,
    // Fixed arrays in scope, by element count: what `a[..]` puts in the slice header it builds.
    arrayLen: HashMap<str, long>,

    // Every `...T` function in the program, by name. Collected before anything is lowered,
    // because a call may come above the declaration it packs for.
    variadics: HashMap<str, long>,
    varSigs: Vec<VarSig>,

    // Every `builtin` declaration, by name: the primitive a call to it is (`BI_...`).
    builtinKinds: HashMap<str, long>,
    asmSeq: long,              // hidden slots a builtin's `asm` writes its result to

    // What the function being lowered returns. A `return` needs its destination's type, not its
    // expression's: those differ wherever a concrete struct is returned as a trait object.
    retKind: Lit,
    retStruct: Sym,
    // The declaration being lowered is an array the next statements write in full
    // (`writtenInFull`): no zero fill.
    skipZero: bool
}

methods Lowerer for Default {
    new -> Lowerer {
        p: IRProgram;
        return Lowerer { ir: p, labels: 0, breakTo: vec![], continueTo: vec![], byRef: map![], arrayLen: map![],
                         variadics: map![], varSigs: vec![],
                         builtinKinds: map![], asmSeq: 0, skipZero: false,
                         retKind: Lit.Void, retStruct: NO_SYM };
    }
}

methods Lowerer {
    // ─── labels ──────────────────────────────────────────────────────────────

    // `.L<n>`: local to the function being lowered, which is why the counter resets with it.
    freshLabel &self -> Sym {
        s: String;
        s.pushStr(".L");
        s.pushLong(self.labels);
        self.labels = self.labels + 1;
        out: Sym = NO_SYM;
        out = internString(s);
        return out;
    }

    emitLabel &self name:Sym -> void {
        in: Instr = instr(IROp.Label);
        in.name = name;
        self.ir.emit(in);
    }
    emitJump &self op:IROp target:Sym cond:Temp -> void {
        in: Instr = instr(op);
        in.name = target;
        in.a = cond;
        self.ir.emit(in);
    }

    // ─── functions ───────────────────────────────────────────────────────────

    lowerProgram &self inout a:Ast page:long -> void {
        n: long = a.blockLen(page);
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.VarDecl) {
                d: VarDeclNode = a.decls.get(st.at);
                self.ir.noteGlobal(d.name, declaredBytes(d));
            }
        }
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.FunctionDef) {
                self.noteVariadic(a, a.fns.get(st.at));
                self.noteHook(a.fns.get(st.at));
                bk: long = builtinOf(a.fns.get(st.at));
                if (bk != 0) { self.builtinKinds.put(nameOf(a.fns.get(st.at).name), bk); }
            }
        }
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            // A generic method's own body is a pattern, not code: its clones carry the concrete
            // types and are what gets emitted. Lowering the pattern would emit calls against
            // type parameters, which is what left a bare `write` in every program that printed.
            if (st.kind == StmtKind.FunctionDef && !a.fns.get(st.at).isTemplate) {
                // Where an error lowering it (or emitting it, later) is reported.
                gPos = a.stmtPos.get(a.stmtIdAt(page, k));
                enterFn(a.fns.get(st.at).name);
                noteFnPos(a.fns.get(st.at).name, gPos);
                self.lowerFunction(a, st.at);
            }
        }
        gPos = 0;
        gCtxFn = NO_SYM;
        gCtxInst = NO_SYM;
        self.carryImages(a);
        self.lowerGlobalInit(a, page);
    }

    // Every image the evaluator computed, in order, so a block's index is the same on both
    // sides. A relocation to a string literal interns it here exactly as a mention in code would.
    carryImages &self inout a:Ast -> void {
        for i in 0..a.images.len() {
            im: ImageNode = a.images.get(i);
            self.ir.addImage(im.isBlock);
            for k in 0..im.byteCount { self.ir.imageByte(a.imageBytes.get(im.firstByte + k)); }
            for k in 0..im.relocCount {
                r: RelocNode = a.relocs.get(im.firstReloc + k);
                target: long = r.target as long;
                if (r.kind == RelocKind.Str) { target = self.ir.internString(r.target); }
                if (r.kind == RelocKind.Block) { target = r.image; }
                self.ir.imageReloc(r.offset, r.kind, target, r.delta);
            }
        }
    }

    // A global's initializer may be any expression, so it is not folded into `.data`: it runs at
    // program start, in declaration order, from a synthetic function `_start` calls before `main`.
    // Except a scalar whose initializer is a constant -- written as one, or folded to one by the
    // evaluator -- which is emitted with its value and needs no code at all. When every global is
    // one of those, there is no `$globalInit`.
    lowerGlobalInit &self inout a:Ast page:long -> void {
        self.labels = 0;
        self.retKind = Lit.Void;
        self.retStruct = NO_SYM;
        first: long = self.ir.code.len();
        firstT: Temp = self.ir.tempKinds.len();   // the first temp this body will own
        // An initializer may allocate: `_start` runs the `@init` hooks (the heap's) before this.
        n: long = a.blockLen(page);
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.VarDecl) {
                d: VarDeclNode = a.decls.get(st.at);
                if (isExternGlobal(d.name)) {
                    // another package's: its own object stores it, and runs its initializer
                } else if (d.init != NO_NODE && self.constantInit(a, d)) {
                    // in .data already
                } else if (d.init != NO_NODE) {
                    // An aggregate global holds its bytes, not a pointer to them. Lowering its
                    // initializer yields the address of wherever it was built, so the bytes have
                    // to be copied in: storing the address instead writes a scratch pointer over
                    // the first field, which for a `Mutex` is the lock flag it is guarded by.
                    if (d.isArray && a.expr(d.init).op == Op.ArrayLit) {
                        self.lowerArrayInto(a, self.addressOfVar(d.name, d.structName), d.init);
                    } else if (storedInline(d.kind, d.structName)) {
                        src: Temp = self.placeOf(a, d.init);
                        dst: Temp = self.addressOfVar(d.name, d.structName);
                        self.copyInto(dst, src, aggregateBytes(d.kind, d.structName));
                    } else {
                        v: Temp = self.lowerExpr(a, d.init);
                        self.storeVar(d.name, v, d.kind);
                    }
                }
            }
        }
        if (self.ir.code.len() == first) { return; }    // nothing to run: no function
        self.ir.emit(instr(IROp.RetVoid));
        // Before the range is claimed: a promotion temp made after this would be numbered past
        // `tempCount` and the allocator would treat it as another function's.
        fp: long = self.ir.reservePromotions(first);
        self.ir.funcs.push(IRFunc { name: initFunctionName(), firstInstr: first,
                                    instrCount: self.ir.code.len() - first,
                                    firstTemp: firstT, tempCount: self.ir.tempKinds.len(),
                                    firstPromo: fp, promoCount: self.ir.promoName.len() - fp,
                                    isPub: gKlibMode, isMain: false, wantsArgs: false, imported: false });
    }

    // `[a, b, c]` into the array at `dst`, element by element: what a `var` global's literal does
    // at startup when the evaluator could not compute it.
    lowerArrayInto &self inout a:Ast dst:Temp lit:NodeId -> void {
        e: Expr = a.expr(lit);
        ln: LitNode = a.lits.get(0);
        match e.payload { Lit(l) { ln = a.lits.get(l); } _ { return; } }
        w: long = typeBytes(e.kind, e.structName);
        for k in 0..ln.initCount {
            v: NodeId = a.inits.get(ln.firstInit + k).value;
            if (storedInline(e.kind, e.structName)) {
                self.copyInto(self.offsetPtr(dst, k * w), self.placeOf(a, v), aggregateBytes(e.kind, e.structName));
            } else {
                self.storeAt(dst, k * w, self.lowerExpr(a, v), storedKind(e.kind, e.structName));
            }
        }
    }

    // A global initialized by a constant -- a scalar literal, or an image the evaluator computed
    // -- is recorded on the program and emitted as data. An image's pointer words name string
    // literals, which are interned here exactly as a mention in code would intern them.
    constantInit &self inout a:Ast d:VarDeclNode -> bool {
        e: Expr = a.expr(d.init);
        if (e.op == Op.Image) {
            match e.payload { Image(i) { self.ir.setGlobalImage(d.name, i); } _ { } }
            return true;
        }
        sk: Lit = storedKind(d.kind, d.structName);
        if (d.isArray || !(isInteger(sk) || d.kind == Lit.Bool || isFloat(sk))) { return false; }
        if (e.op != Op.Literal) { return false; }
        match e.payload {
            Num(v) { self.ir.setGlobalInit(d.name, v); return true; }
            // A float literal as written: its bits, at the global's width. An immutable global is
            // in `.rodata`, which nothing may write at startup, so it has to be data.
            Text(t) {
                if (isFloat(sk)) { self.ir.setGlobalInit(d.name, decimalToFloat(nameOf(t), sk == Lit.Float)); return true; }
            }
            _ { }
        }
        return false;
    }

    lowerFunction &self inout a:Ast at:long -> void {
        f: FnNode = a.fns.get(at);
        // Declared, not defined. There is no body to lower and no `IRFunc` to make; the name is
        // recorded so the emitter can write an `extern` directive for it if anything reaches it.
        // (A dependency's body not yet read is a body, and is the dependency's to compile.)
        if (!hasBody(f)) {
            self.ir.externs.push(f.name);
            return;
        }
        // A dependency's function: compiled into its own package's object, whose `.klib` listed
        // the symbol, so the emitter already treats it as defined elsewhere.
        if (isExternFn(at)) { return; }
        // A lazy method nothing here reached: not checked, so not compiled; nothing calls it.
        if (isUnchecked(at)) { return; }
        // What another object may call. A package build exports every function its source
        // defines, whatever its visibility: a generic instance stamped in a dependent, or a
        // macro's expansion there, may call any of them, and the linker only sees symbols.
        exported: bool = f.visibility == Vis.Pub;
        if (gKlibMode) { exported = isOwnSourceFn(a, at); }
        self.labels = 0;
        self.retKind = f.returnKind;
        self.retStruct = f.returnStruct;
        self.byRef.clear();
        self.arrayLen.clear();
        first: long = self.ir.code.len();
        firstT: Temp = self.ir.tempKinds.len();   // the first temp this body will own

        // A struct return does not fit in a register, so the caller passes the address to write it
        // to as a hidden first argument, and every real parameter shifts along by one.
        if (returnedByPointer(f.returnKind, f.returnStruct)) {
            self.ir.noteSlot(sretSym(), 8);
            self.noteByRef(sretSym());
            sr: Temp = self.ir.newTemp(Lit.Ptr, f.returnStruct);
            sd: Instr = instr(IROp.Load);
            sd.dst = sr;
            sd.name = sretSym();
            sd.kind = Lit.Ptr;
            sd.paramSeed = true;
            self.ir.emit(sd);
        }

        // Each parameter arrives in a register and is stored to its slot, so the body reads it by
        // name like any other local. `mem2reg` is what later takes the store back out.
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            if (p.isArray) { self.arrayLen.put(nameOf(p.name), p.count); }
            // A by-value struct is the callee's own: it arrives as a pointer to the caller's
            // copy and the prologue copies the bytes into storage of its own, so writing the
            // parameter cannot write the caller's object. A borrow (`&self`, `inout`, and a
            // read parameter the checker retyped) is `Lit.Ref` and keeps the pointer, which is
            // the whole difference between the two. `str`, a slice and a trait object stay by
            // reference: their value is the address of the pair, and the fat-pointer paths read
            // it through the slot.
            byValue: bool = passedByPointer(p.kind, p.structName) && byValueAggregate(p.kind);
            if (byValue && !p.isArray) {
                self.ir.noteSlot(p.name, declaredBytes(p));
            } else if (passedByPointer(p.kind, p.structName) && !p.isArray) {
                self.noteByRef(p.name);
                self.ir.noteSlot(p.name, 8);
            } else { self.ir.noteSlot(p.name, declaredBytes(p)); }
            // A borrow of a float (`&self` in `methods f64`) is the float itself, typed so: the
            // arithmetic on it is a float's, and it arrives where a float argument does.
            pk: Lit = p.kind;
            if (pk == Lit.Ref && p.structName != NO_SYM && namesScalar(nameOf(p.structName))
                && isFloat(scalarNamed(nameOf(p.structName)))) { pk = scalarNamed(nameOf(p.structName)); }
            t: Temp = self.ir.newTemp(pk, p.structName);
            if (pk != p.kind) { self.ir.notePointee(t, NO_SYM); }
            ld: Instr = instr(IROp.Load);
            ld.dst = t;
            ld.name = p.name;
            // The prologue reads this to decide whether the register holds the value or a pointer
            // to it, so a backed enum has to say the width it is rather than the `Lit.Struct` the
            // parser gives every named type: the register holds the integer, not its address.
            ld.kind = pk;
            if (namedScalar(p.kind, p.structName)) { ld.kind = namedScalarBacking(p.structName); }
            ld.structName = p.structName;
            // How many bytes that copy moves, from the declaration. Not from `slotBytesOf`: the
            // slot table is program-wide and keyed by name, taking the largest claim any function
            // made for that name, fine for reserving frame space, and wildly wrong as the length
            // of a copy.
            if (byValue && !p.isArray) { ld.imm = declaredBytes(p); }
            ld.paramSeed = true;
            self.ir.emit(ld);
        }

        isMain: bool = nameEndsWith(nameOf(f.name), "::main") || nameOf(f.name) == "main";

        self.lowerBlock(a, f.body);

        // A body that falls off its end returns nothing. Harmless when it cannot be reached.
        if (f.returnKind == Lit.Void) { self.ir.emit(instr(IROp.RetVoid)); }

        takesArgs: bool = false;

        if (isMain && f.argCount > 0) {
            p0: VarDeclNode = a.paramAt(f, 0);
            takesArgs = p0.isVariadic && p0.elemKind == Lit.Str;
        }
        fp: long = self.ir.reservePromotions(first);
        self.ir.funcs.push(IRFunc { name: f.name, firstInstr: first,
                                    instrCount: self.ir.code.len() - first,
                                    firstTemp: firstT, tempCount: self.ir.tempKinds.len(),
                                    firstPromo: fp, promoCount: self.ir.promoName.len() - fp,
                                    isPub: exported,
                                    isMain: isMain, wantsArgs: takesArgs, imported: false });
    }

    // ─── statements ──────────────────────────────────────────────────────────

    lowerBlock &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in 0..n {
            a.enterStmt(a.stmtIdAt(b, k));        // where an internal error here is reported
            st: Stmt = a.stmtAt(b, k);
            // A local array the next statements plainly write in full before anything reads it
            // starts as whatever they write: its zero fill would only be overwritten.
            self.skipZero = st.kind == StmtKind.VarDecl && writtenInFull(a, b, k);
            self.lowerStmt(a, st);
            self.skipZero = false;
        }
    }

    lowerStmt &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            self.ir.noteSlot(d.name, declaredBytes(d));
            // A ref local's slot holds the address of what it borrows, exactly as a by-pointer
            // parameter's does: `for r: &Res in it` binds one, and so does a borrow taken out of
            // a call. Saying so here is what makes reading the name a load of the pointer rather
            // than an `lea` of the eight bytes holding it. Per declaration, not per name: a value
            // a sibling scope declares under the same name (`for p in v { }` and then
            // `{ p: P = ...; }`) is a value again, and reading it through the old borrow wrote
            // the collection.
            if (d.kind == Lit.Ref && !d.isArray) { self.noteByRef(d.name); }
            else { self.byRef.remove(nameOf(d.name)); }
            if (d.isArray) { self.arrayLen.put(nameOf(d.name), d.count); }
            // A local array declared without a value starts as zero bytes, as a struct literal's
            // omitted fields do; the stack held whatever the last frame left there. An array of
            // a type that owns something is filled by its `Default` instead (the ownership pass's
            // element loop), so it is not zeroed first.
            if (d.init == NO_NODE && d.isArray && d.count > 0 && !self.skipZero
                && !(d.kind == Lit.Struct && gReg.needsDrop(d.structName))) {
                z: Instr = instr(IROp.AggZero);
                z.a = self.addressOfVar(d.name, d.structName);
                z.imm = declaredBytes(d);
                self.ir.emit(z);
            }
            if (d.init != NO_NODE) {
                // An aggregate initializer is a block copy into the variable's storage. Storing
                // the value would store the address of someone else's copy, and both names would
                // then be the same object.
                if (storedInline(d.kind, d.structName)) {
                    src: Temp = self.lowerAggValue(a, d.init, d.kind, d.structName);
                    self.copyInto(self.addressOfVar(d.name, d.structName), src,
                                  aggregateBytes(d.kind, d.structName));
                } else {
                    v: Temp = self.lowerExpr(a, d.init);
                    self.storeVar(d.name, v, d.kind);
                }
            }
            return;
        }
        if (st.kind == StmtKind.Expr) { self.lowerExpr(a, a.exprStmts.get(st.at).value); return; }
        if (st.kind == StmtKind.Return) {
            r: ReturnNode = a.returns.get(st.at);
            if (r.value == NO_NODE) { self.ir.emit(instr(IROp.RetVoid)); return; }
            if (returnedByPointer(self.retKind, self.retStruct)) {
                src: Temp = self.lowerAggValue(a, r.value, self.retKind, self.retStruct);
                dst: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
                ld: Instr = instr(IROp.Load);
                ld.dst = dst;
                ld.name = sretSym();
                ld.kind = Lit.Ptr;
                self.ir.emit(ld);
                cp: Instr = instr(IROp.AggCopy);
                cp.a = dst;
                cp.b = src;
                cp.imm = aggregateBytes(self.retKind, self.retStruct);
                self.ir.emit(cp);
                rv: Instr = instr(IROp.Ret);
                rv.a = dst;
                rv.kind = Lit.Ptr;
                self.ir.emit(rv);
                return;
            }
            // `-> &T` hands back the address of the place named, not what is in it: `return *p`
            // returns `p`. The checker has already made sure that place outlives the call.
            v: Temp = NO_TEMP;
            if (self.retKind == Lit.Ref) { v = self.baseAddress(a, r.value); }
            if (v == NO_TEMP) { v = self.lowerExpr(a, r.value); }
            in: Instr = instr(IROp.Ret);
            in.a = v;
            in.kind = self.ir.kindOf(v);
            self.ir.emit(in);
            return;
        }
        if (st.kind == StmtKind.If)    { self.lowerIf(a, st.at); return; }
        if (st.kind == StmtKind.Match) { self.lowerMatch(a, st.at); return; }
        if (st.kind == StmtKind.While) { self.lowerWhile(a, st.at); return; }
        if (st.kind == StmtKind.Loop)  { self.lowerLoop(a, a.blockStmts.get(st.at).body); return; }
        if (st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
            self.lowerBlock(a, a.blockStmts.get(st.at).body);
            return;
        }
        // `with` is a block by the time it gets here: the checker put the guard's construction in
        // front of the body and its release after.
        if (st.kind == StmtKind.With) { self.lowerBlock(a, a.withs.get(st.at).body); return; }
        if (st.kind == StmtKind.Asm) { self.lowerAsm(a, st.at); return; }
        // A struct declaration is a fact about types, not code: the registry already holds it.
        if (st.kind == StmtKind.StructDecl) { return; }
        if (st.kind == StmtKind.Break) {
            if (self.breakTo.len() > 0) { self.emitJump(IROp.Jmp, self.breakTo.last(), NO_TEMP); }
            return;
        }
        if (st.kind == StmtKind.Continue) {
            if (self.continueTo.len() > 0) { self.emitJump(IROp.Jmp, self.continueTo.last(), NO_TEMP); }
            return;
        }
    }

    // A condition as control flow: fall through when it holds, jump to `falseL` when it does not.
    //
    // `lowerShortCircuit` produces a value, and for `i < 0 || i >= n` that costs two `setcc`s, two
    // widenings and a merge, and then the `if` compares the value it built against zero and
    // branches on that. As control flow the same condition is two compares and two conditional
    // jumps, and nothing is materialised at all. `Vec.at` is the shape that made it worth doing;
    // every `&&` and `||` written in a condition gets it.
    branchUnless &self inout a:Ast id:NodeId falseL:Sym -> void {
        e: Expr = a.expr(id);
        if (e.op == Op.LogicalAnd) {
            self.branchUnless(a, e.left, falseL);
            self.branchUnless(a, e.right, falseL);
            return;
        }
        if (e.op == Op.LogicalOr) {
            // The left holding is enough for the whole thing, so jump past the right to where the
            // fall-through resumes.
            okL: Sym = self.freshLabel();
            self.branchIf(a, e.left, okL);
            self.branchUnless(a, e.right, falseL);
            self.emitLabel(okL);
            return;
        }
        if (e.op == Op.LogicalNot) {
            p: Payload = e.payload;
            match p { Sub(v) { self.branchIf(a, v, falseL); return; } _ { } }
        }
        if (isComparison(e.op)) { self.compareJump(a, e, falseL, true); return; }
        c: Temp = self.lowerExpr(a, id);
        self.emitJump(IROp.Jz, falseL, c);
    }

    // The mirror: jump to `trueL` when the condition holds, fall through when it does not.
    branchIf &self inout a:Ast id:NodeId trueL:Sym -> void {
        e: Expr = a.expr(id);
        if (e.op == Op.LogicalOr) {
            self.branchIf(a, e.left, trueL);
            self.branchIf(a, e.right, trueL);
            return;
        }
        if (e.op == Op.LogicalAnd) {
            noL: Sym = self.freshLabel();
            self.branchUnless(a, e.left, noL);
            self.branchIf(a, e.right, trueL);
            self.emitLabel(noL);
            return;
        }
        if (e.op == Op.LogicalNot) {
            p: Payload = e.payload;
            match p { Sub(v) { self.branchUnless(a, v, trueL); return; } _ { } }
        }
        if (isComparison(e.op)) { self.compareJump(a, e, trueL, false); return; }
        c: Temp = self.lowerExpr(a, id);
        nz: Temp = self.notOf(c);
        self.emitJump(IROp.Jz, trueL, nz);
    }

    // One comparison, straight to a conditional jump. The operation's type is the operands common
    // type, exactly as the value form takes it: that is what decides signed against unsigned, and
    // taking the left one would order `long` against `u64` by the wrong rule.
    compareJump &self inout a:Ast e:Expr to:Sym negate:bool -> void {
        l: Temp = self.lowerExpr(a, e.left);
        r: Temp = self.lowerExpr(a, e.right);
        op: IROp = opFor(e.op);
        // Over floats `!(a < b)` is not `a >= b`: both are false when either is a NaN. So the
        // jump on a comparison not holding is a jump on its value being zero.
        ck: Lit = commonKind(self.ir.kindOf(l), self.ir.kindOf(r));
        if (negate && isFloat(ck)) {
            c: Temp = self.ir.newTemp(Lit.Bool, NO_SYM);
            ci: Instr = instr(op);
            ci.dst = c; ci.a = l; ci.b = r; ci.kind = ck;
            self.ir.emit(ci);
            self.emitJump(IROp.Jz, to, c);
            return;
        }
        if (negate) { op = negateCompare(op); }
        j: Instr = instr(IROp.Jcc);
        j.a = l;
        j.b = r;
        j.cmpOp = op;
        j.kind = commonKind(self.ir.kindOf(l), self.ir.kindOf(r));
        j.name = to;
        self.ir.emit(j);
    }

    // `if (c) { A } else { B }` becomes: test, jump-if-zero to else, A, jump to end, else: B, end:
    lowerIf &self inout a:Ast at:long -> void {
        n: IfNode = a.ifs.get(at);

        elseL: Sym = self.freshLabel();
        endL:  Sym = self.freshLabel();
        self.branchUnless(a, n.cond, elseL);
        self.lowerBlock(a, n.body);
        self.emitJump(IROp.Jmp, endL, NO_TEMP);
        self.emitLabel(elseL);
        if (n.elseIf >= 0) { self.lowerIf(a, n.elseIf); }
        self.emitLabel(endL);
    }

    // A match is a chain of tag tests, which is what an if/else-if chain lowers to as well.
    // Every arm but the last tests; the last is reached by elimination (it is the `_`, or
    // exhaustiveness leaves it as the only possibility) so it costs no compare at all. Each
    // arm's payload bindings are already ordinary locals at the head of its block.
    lowerMatch &self inout a:Ast at:long -> void {
        m: MatchNode = a.matches.get(at);
        endL: Sym = self.freshLabel();
        k: long = 0;
        while (k < m.armCount) {
            arm: ArmNode = a.arms.get(m.firstArm + k);
            if (arm.test == NO_NODE) { self.lowerBlock(a, arm.body); k = m.armCount; continue; }
            nextL: Sym = self.freshLabel();
            self.branchUnless(a, arm.test, nextL);
            self.lowerBlock(a, arm.body);
            self.emitJump(IROp.Jmp, endL, NO_TEMP);
            self.emitLabel(nextL);
            k = k + 1;
        }
        self.emitLabel(endL);
    }

    // The condition is re-tested at the top of each turn, and `continue` jumps to the step when
    // there is one, which is why a `for` is a while with a step rather than a desugaring.
    lowerWhile &self inout a:Ast at:long -> void {
        w: WhileNode = a.whiles.get(at);
        topL:  Sym = self.freshLabel();
        stepL: Sym = self.freshLabel();
        endL:  Sym = self.freshLabel();

        self.emitLabel(topL);
        self.branchUnless(a, w.cond, endL);

        self.breakTo.push(endL);
        self.continueTo.push(stepL);
        self.lowerBlock(a, w.body);
        self.breakTo.pop();
        self.continueTo.pop();

        self.emitLabel(stepL);
        if (w.step >= 0) { self.lowerBlock(a, w.step); }
        self.emitJump(IROp.Jmp, topL, NO_TEMP);
        self.emitLabel(endL);
    }

    lowerLoop &self inout a:Ast body:long -> void {
        topL: Sym = self.freshLabel();
        endL: Sym = self.freshLabel();
        self.emitLabel(topL);
        self.breakTo.push(endL);
        self.continueTo.push(topL);
        self.lowerBlock(a, body);
        self.breakTo.pop();
        self.continueTo.pop();
        self.emitJump(IROp.Jmp, topL, NO_TEMP);
        self.emitLabel(endL);
    }

    storeVar &self name:Sym v:Temp k:Lit -> void {
        in: Instr = instr(IROp.Store);
        in.name = name;
        in.a = v;
        in.kind = k;
        in.structName = self.ir.structOf(v);
        in.isGlobal = self.ir.isGlobalName(name);
        self.ir.emit(in);
    }

    // ─── expressions ─────────────────────────────────────────────────────────

    // Lower `id` and return the temp holding its value.
    lowerExpr &self inout a:Ast id:NodeId -> Temp {
        if (id == NO_NODE) { return NO_TEMP; }
        e: Expr = a.expr(id);

        // `sizeof(T)`: a long constant; T is on the leaf under it (`Ast.sizeofNode`).
        if (e.op == Op.Sizeof) {
            t: Expr = a.measuredOf(id);
            return self.constTemp(typeBytes(t.kind, t.structName), Lit.Long);
        }
        if (e.op == Op.Assignment) { return self.lowerAssign(a, id); }
        if (e.op == Op.LogicalAnd || e.op == Op.LogicalOr) { return self.lowerShortCircuit(a, id); }
        // `&x` is where the value lives, not what it holds: a variable's slot, a field's offset
        // from its base, an element's from the array's. `lowerAddress` answers all three.
        if (e.op == Op.AddressOf) {
            inner: NodeId = self.subNode(a, id);
            // `&isOdd` is the address of a function: a label, not a slot. Taken as a variable's
            // address it handed out a pointer into this frame, and the call through it jumped
            // into the stack.
            if (inner != NO_NODE && e.kind == Lit.Fn) {
                fname: Sym = NO_SYM;
                q: Payload = a.expr(inner).payload;
                match q { Name(n) { fname = n; } _ { } }
                if (fname != NO_SYM) {
                    t: Temp = self.ir.newTemp(Lit.Fn, e.structName);
                    fa: Instr = instr(IROp.FnAddr);
                    fa.dst = t; fa.name = fname; fa.kind = Lit.Ptr;
                    self.ir.emit(fa);
                    return t;
                }
            }
            if (inner != NO_NODE) {
                // `&__cl.x` on a ref forwards the borrow rather than taking a second one: the
                // address to hand on is the one already held, not where it is held. That covers
                // a captured `&S` field and a parameter inference retyped to a borrow alike.
                at: Temp = NO_TEMP;
                if (a.expr(inner).kind == Lit.Ref) { at = self.lowerExpr(a, inner); }
                else { at = self.lowerAddress(a, inner); }
                if (at != NO_TEMP) { return at; }
            }
        }
        // `*p`: a load of the pointee, at the pointee's width.
        if (e.op == Op.Deref) {
            inner: NodeId = self.subNode(a, id);
            if (inner != NO_NODE) {
                t: Temp = self.ir.newTemp(e.kind, e.structName);
                ld: Instr = instr(IROp.PtrLoad);
                ld.dst = t;
                ld.a = self.lowerExpr(a, inner);
                ld.imm = 0;
                ld.kind = e.kind;
                self.ir.emit(ld);
                return t;
            }
        }

        p: Payload = e.payload;
        // A float literal: its spelling, rounded to its width once, here.
        if (e.op == Op.Literal && isFloat(e.kind)) {
            match p {
                Text(s) { return self.constTemp(decimalToFloat(nameOf(s), e.kind == Lit.Float), e.kind); }
                _ { }
            }
        }
        match p {
            Num(n) {
                t: Temp = self.ir.newTemp(e.kind, e.structName);
                in: Instr = instr(IROp.Const);
                in.dst = t;
                in.imm = n;
                in.kind = e.kind;
                self.ir.emit(in);
                return t;
            }
            Name(n) {
                // An aggregate does not fit in a register: its value is the address of where it
                // lives, which is also what every reader of one expects to be handed.
                if (passedByPointer(e.kind, e.structName) || self.arrayCount(n) != NOT_FOUND) {
                    return self.addressOfVar(n, e.structName);
                }
                t: Temp = self.ir.newTemp(e.kind, e.structName);
                in: Instr = instr(IROp.Load);
                in.dst = t;
                in.name = n;
                in.kind = e.kind;
                in.structName = e.structName;
                in.isGlobal = self.ir.isGlobalName(n);
                self.ir.emit(in);
                return t;
            }
            Text(t) {
                // A `str` value is a 16-byte {ptr, len} pair in `.data`; the temp holds its
                // address, and reading `.ptr` or `.len` is a load through it.
                at: long = self.ir.internString(t);
                v: Temp = self.ir.newTemp(Lit.Str, NO_SYM);
                in: Instr = instr(IROp.StrLitVal);
                in.dst = v;
                in.imm = at;
                in.kind = Lit.Str;
                self.ir.emit(in);
                return v;
            }
            Call(c) { return self.lowerCall(a, id, c); }
            Sub(v)  {
                if (e.op == Op.MakeTraitObj) { return self.lowerTraitObj(a, id); }
                return self.lowerUnary(a, id, v);
            }
            Field(_) { return self.lowerFieldRead(a, id); }
            Index(_) { return self.lowerIndexRead(a, id); }
            Lit(l)   { return self.lowerStructLit(a, id, l); }
            _ { }
        }

        if (e.left != NO_NODE && e.right != NO_NODE) {
            // `-x` over a float flips the sign bit, of a zero and a NaN too: an `xor`, which the
            // emitter does in the integer registers a float lives in.
            if (e.op == Op.Subtraction && isNegationMark(a.expr(e.left))) {
                v: Temp = self.lowerExpr(a, e.right);
                k: Lit = self.ir.kindOf(v);
                sign: long = F64_SIGN;
                if (k == Lit.Float) { sign = F32_SIGN; }
                t: Temp = self.ir.newTemp(k, NO_SYM);
                x: Instr = instr(IROp.BXor);
                x.dst = t; x.a = v; x.b = self.constTemp(sign, k); x.kind = k;
                self.ir.emit(x);
                return t;
            }
            l: Temp = self.lowerExpr(a, e.left);
            r: Temp = self.lowerExpr(a, e.right);
            // `p + n` on a `*T` steps whole elements and `q - p` counts them, both scaled by the
            // pointee the temp carries. Without it a pointer walks by bytes: `boxes + a` over
            // 24-byte boxes landed eight bytes in, and read a value's address as its tag. Asked
            // after both operands are lowered, because whether this is pointer arithmetic is a
            // fact about the values, and a raw address that happens to be spelled `*T` is not one.
            scaled: Temp = self.lowerPtrArith(a, id, l, r);
            if (scaled != NO_TEMP) { return scaled; }
            // The operation's type is the common type of the two operands, not the left one's:
            // it decides whether a shift, a division and a comparison are signed, and how wide the
            // result wraps. `long / int` taking the left operand's type would divide correctly and
            // then truncate the answer to thirty-two bits.
            common: Lit = commonKind(self.ir.kindOf(l), self.ir.kindOf(r));
            t: Temp = self.ir.newTemp(e.kind, e.structName);
            in: Instr = instr(opFor(e.op));
            in.dst = t;
            in.a = l;
            in.b = r;
            // The operation's type is the operands' type; the destination's is what sizes the
            // write-back, and for a comparison those differ.
            in.kind = common;
            self.ir.emit(in);
            return t;
        }
        return NO_TEMP;
    }

    lowerUnary &self inout a:Ast id:NodeId v:NodeId -> Temp {
        e: Expr = a.expr(id);
        inner: Temp = self.lowerExpr(a, v);
        if (e.op == Op.Cast) {
            t: Temp = self.ir.newTemp(e.kind, e.structName);
            // Between a named scalar and the 64-bit integer it is (`m as long` over a distinct
            // long, `n as Sym`) a cast is the same bits: a copy, which the copy passes erase, where
            // a `Convert` would cost a trip through rax for nothing.
            to: Lit = storedKind(e.kind, e.structName);
            if ((to == Lit.Long || to == Lit.U64)
                && to == storedKind(self.ir.kindOf(inner), self.ir.structOf(inner))) {
                mv: Instr = instr(IROp.Mov);
                mv.dst = t; mv.a = inner; mv.kind = e.kind; mv.structName = e.structName;
                self.ir.emit(mv);
                return t;
            }
            in: Instr = instr(IROp.Convert);
            in.dst = t;
            in.a = inner;
            in.kind = e.kind;
            in.fromKind = self.ir.kindOf(inner);
            in.toKind = e.kind;
            // With a float on either side the conversion is a value's, so a distinct type is
            // named by what it is stored as: `3 as Meters` over an `f64` is `3.0`.
            fk: Lit = storedKind(self.ir.kindOf(inner), self.ir.structOf(inner));
            if (isFloat(fk) || isFloat(to)) { in.fromKind = fk; in.toKind = to; }
            self.ir.emit(in);
            return t;
        }
        if (e.op == Op.BitwiseNot) {
            t: Temp = self.ir.newTemp(e.kind, e.structName);
            in: Instr = instr(IROp.BNot);
            in.dst = t;
            in.a = inner;
            in.kind = self.ir.kindOf(inner);
            self.ir.emit(in);
            return t;
        }
        if (e.op == Op.LogicalNot) {
            // `!x` is `x == 0`, which is one compare rather than a branch.
            zero: Temp = self.ir.newTemp(self.ir.kindOf(inner), NO_SYM);
            z: Instr = instr(IROp.Const);
            z.dst = zero;
            z.imm = 0;
            z.kind = self.ir.kindOf(inner);
            self.ir.emit(z);
            t: Temp = self.ir.newTemp(Lit.Bool, NO_SYM);
            in: Instr = instr(IROp.CmpEq);
            in.dst = t;
            in.a = inner;
            in.b = zero;
            in.kind = self.ir.kindOf(inner);
            self.ir.emit(in);
            return t;
        }
        return inner;
    }

    lowerAssign &self inout a:Ast id:NodeId -> Temp {
        e: Expr = a.expr(id);
        lhs0: Expr = a.expr(e.left);
        // Assigning an aggregate copies its bytes into the destination's storage. A ref holds a
        // pointer, so assigning one is an ordinary word store.
        if (storedInline(lhs0.kind, lhs0.structName)) {
            src: Temp = self.lowerAggValue(a, e.right, lhs0.kind, lhs0.structName);
            dst: Temp = self.lowerAddress(a, e.left);
            if (dst != NO_TEMP) { self.copyInto(dst, src, aggregateBytes(lhs0.kind, lhs0.structName)); }
            return src;
        }
        v: Temp = self.lowerExpr(a, e.right);
        lhs: Expr = a.expr(e.left);
        p: Payload = lhs.payload;
        match p {
            Name(n)  { self.storeVar(n, v, lhs.kind); }
            Field(_) { self.lowerFieldWrite(a, e.left, v); }
            Index(_) { self.lowerIndexWrite(a, e.left, v); }
            // `*p = v`: a store through a pointer. The width is the pointee's, which is what
            // the dereference already typed this node as.
            Sub(inner) {
                if (lhs.op == Op.Deref) {
                    st: Instr = instr(IROp.PtrStore);
                    st.a = self.lowerExpr(a, inner);
                    st.b = v;
                    st.imm = 0;
                    st.kind = lhs.kind;
                    self.ir.emit(st);
                }
            }
            _ { }
        }
        return v;
    }

    // `&&` and `||` must not evaluate their right operand unless they have to, so they are control
    // flow rather than an operation: the result variable is set on whichever path is taken.
    lowerShortCircuit &self inout a:Ast id:NodeId -> Temp {
        e: Expr = a.expr(id);
        res: Temp = self.ir.newTemp(Lit.Bool, NO_SYM);
        shortL: Sym = self.freshLabel();
        endL:   Sym = self.freshLabel();

        l: Temp = self.lowerExpr(a, e.left);
        self.moveTo(res, l);
        if (e.op == Op.LogicalAnd) { self.emitJump(IROp.Jz, shortL, l); }
        else {
            // `||` short-circuits on true, and the only test the IR has is jump-if-zero, so branch
            // past the right operand when the left is nonzero by testing its negation.
            nz: Temp = self.notOf(l);
            self.emitJump(IROp.Jz, shortL, nz);
        }
        r: Temp = self.lowerExpr(a, e.right);
        self.moveTo(res, r);
        self.emitJump(IROp.Jmp, endL, NO_TEMP);
        self.emitLabel(shortL);
        self.emitLabel(endL);
        return res;
    }

    notOf &self v:Temp -> Temp {
        zero: Temp = self.ir.newTemp(self.ir.kindOf(v), NO_SYM);
        z: Instr = instr(IROp.Const);
        z.dst = zero;
        z.imm = 0;
        z.kind = self.ir.kindOf(v);
        self.ir.emit(z);
        t: Temp = self.ir.newTemp(Lit.Bool, NO_SYM);
        in: Instr = instr(IROp.CmpEq);
        in.dst = t;
        in.a = v;
        in.b = zero;
        in.kind = self.ir.kindOf(v);
        self.ir.emit(in);
        return t;
    }

    moveTo &self dst:Temp src:Temp -> void {
        in: Instr = instr(IROp.Mov);
        in.dst = dst;
        in.a = src;
        in.kind = self.ir.kindOf(dst);
        self.ir.emit(in);
    }

    // One argument. An aggregate goes as its address (it does not fit in a register) and
    // everything else as its value. A ref is both: it travels as an address, and its value already
    // is that address, so it goes as a value. Taking its address instead hands over the eight
    // bytes that hold the pointer, which for a closure's captured `&S` is the closure struct.
    lowerArg &self inout a:Ast id:NodeId -> Temp {
        e: Expr = a.expr(id);
        if (storedInline(e.kind, e.structName)) {
            addr: Temp = self.lowerAddress(a, id);
            if (addr != NO_TEMP) { return addr; }
        }
        return self.lowerExpr(a, id);
    }

    // `x.method(args)` where x is a trait object. The receiver is 16 bytes of {data, vtable}:
    // the data half becomes the callee's `self`, and the method's address is loaded out of the
    // vtable half at the slot the checker recorded. Everything else about the call is ordinary.
    lowerDispatch &self inout a:Ast id:NodeId c:long -> Temp {
        e: Expr = a.expr(id);
        cn: CallNode = a.calls.get(c);
        obj: Temp = self.lowerAddress(a, cn.receiver);       // the {data, vtable} pair itself

        data: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
        ld: Instr = instr(IROp.PtrLoad);
        ld.dst = data; ld.a = obj; ld.imm = 0; ld.kind = Lit.Ptr;
        self.ir.emit(ld);

        vt: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
        lv: Instr = instr(IROp.PtrLoad);
        lv.dst = vt; lv.a = obj; lv.imm = 8; lv.kind = Lit.Ptr;
        self.ir.emit(lv);

        fn: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
        lf: Instr = instr(IROp.PtrLoad);
        lf.dst = fn; lf.a = vt; lf.imm = cn.slot * 8; lf.kind = Lit.Ptr;
        self.ir.emit(lf);

        argTemps: Vec<Temp>;
        for k in 0..cn.argCount { argTemps.push(self.lowerArg(a, a.argAt(cn, k))); }

        ret: Temp = NO_TEMP;
        if (returnedByPointer(e.kind, e.structName)) {
            slot: long = self.ir.addAggSlot(aggregateBytes(e.kind, e.structName));
            ret = self.ir.newTemp(Lit.Ptr, e.structName);
            sl: Instr = instr(IROp.AggSlot);
            sl.dst = ret; sl.imm = slot; sl.kind = Lit.Ptr;
            self.ir.emit(sl);
        }
        first: long = self.ir.args.len();
        if (ret != NO_TEMP) { self.ir.args.push(ret); }
        self.ir.args.push(data);                              // the receiver, as `self`
        self.ir.args.extend(argTemps);

        t: Temp = NO_TEMP;
        if (returnedByPointer(e.kind, e.structName)) { t = ret; }
        else if (e.kind != Lit.Void) { t = self.ir.newTemp(e.kind, e.structName); }
        in: Instr = instr(IROp.CallIndirect);
        in.dst = t; in.a = fn;
        in.firstArg = first;
        in.argCount = self.ir.args.len() - first;
        in.kind = e.kind;
        self.ir.emit(in);
        return t;
    }

    // A concrete value seen as a trait object: sixteen bytes holding its address and the address
    // of the vtable for its implementation of that trait.
    lowerTraitObj &self inout a:Ast id:NodeId -> Temp {
        e: Expr = a.expr(id);
        inner: NodeId = NO_NODE;
        p: Payload = e.payload;
        match p { Sub(s) { inner = s; } _ { } }
        return self.coerceTraitObj(a, inner, e.structName);
    }

    // An aggregate value flowing into an aggregate destination. When the destination is a trait
    // object and the value is a concrete struct, the {data, vtable} pair has to be built here.
    // The checker wraps a call argument and a struct-literal field in a `MakeTraitObj` for this,
    // but a declaration, an assignment and a return learn their destination's type only at
    // lowering, and copying sixteen bytes of the struct over the pair leaves the vtable half
    // holding whatever the struct's second word was, which the first dispatch calls through.
    lowerAggValue &self inout a:Ast id:NodeId want:Lit wantName:Sym -> Temp {
        if (want == Lit.TraitObj && wantName != NO_SYM) {
            k: Lit = a.expr(id).kind;
            if (k == Lit.Struct || k == Lit.Ref) { return self.coerceTraitObj(a, id, wantName); }
        }
        return self.placeOf(a, id);
    }

    // Where an aggregate expression's bytes are. `lowerAddress` declines some expressions by
    // answering NO_TEMP, and the value path handles those instead, but for a call and for a
    // literal it does not decline, it lowers, and a call yielding no temp comes back NO_TEMP
    // having already been emitted. Retrying that as a value ran it a second time: `q: Pair =
    // p.clone()` cloned twice and copied neither answer into `q`. An expression is lowered once,
    // so whether a retry is allowed has to be decided from the shape of the node, before it.
    placeOf &self inout a:Ast id:NodeId -> Temp {
        if (id == NO_NODE) { return NO_TEMP; }
        p: Payload = a.expr(id).payload;
        alreadyLowered: bool = false;
        match p {
            Call(_) { alreadyLowered = true; }
            Lit(_)  { alreadyLowered = true; }
            _ { }
        }
        src: Temp = self.lowerAddress(a, id);
        if (src == NO_TEMP && !alreadyLowered) { src = self.lowerExpr(a, id); }
        return src;
    }

    // The pair itself: the value's address, then the address of the vtable for its implementation
    // of that trait, in a fresh sixteen-byte scratch slot.
    coerceTraitObj &self inout a:Ast inner:NodeId trait:Sym -> Temp {
        // `baseAddress`, not `lowerAddress`: the concrete value may be reached through a borrow,
        // and a borrow's address is what it holds.
        data: Temp = self.baseAddress(a, inner);
        concrete: Sym = a.expr(inner).structName;
        self.noteTraitImpl(concrete, trait);

        slot: long = self.ir.addAggSlot(16);
        obj: Temp = self.ir.newTemp(Lit.Ptr, trait);
        sl: Instr = instr(IROp.AggSlot);
        sl.dst = obj; sl.imm = slot; sl.kind = Lit.Ptr;
        self.ir.emit(sl);

        st: Instr = instr(IROp.PtrStore);
        st.a = obj; st.b = data; st.imm = 0; st.kind = Lit.Ptr;
        self.ir.emit(st);

        vt: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
        va: Instr = instr(IROp.VtableAddr);
        va.dst = vt; va.name = intern(vtableName(concrete, trait)); va.kind = Lit.Ptr;
        self.ir.emit(va);

        sv: Instr = instr(IROp.PtrStore);
        sv.a = obj; sv.b = vt; sv.imm = 8; sv.kind = Lit.Ptr;
        self.ir.emit(sv);
        return obj;
    }

    // The table this coercion names has to exist. The checker registers an impl of the exact
    // trait instantiation wherever it builds a trait object, but the destinations it does not
    // cover reach `coerceTraitObj` instead, and an impl nobody registered is a table nobody
    // emits, which surfaces as an undefined symbol at assembly rather than as anything the
    // compiler says. Emission reads the registry, so recording it here is in time.
    noteTraitImpl &self concrete:Sym trait:Sym -> void {
        if (concrete == NO_SYM || trait == NO_SYM) { return; }
        tr: TraitRef = TraitRef { name: trait, firstArg: 0, argCount: 0 };
        if (gReg.implementsTrait(concrete, tr)) { return; }
        at: long = gReg.findTrait(nameOf(trait));
        if (at < 0) { return; }
        t: TraitDef = gReg.traitDef(at);
        fns: Vec<Sym>;
        carried: bool = gReg.flatCarries(concrete, tr);
        for k in 0..t.methodCount {
            fns.push(implFnNameAs(concrete, tr, gReg.traitMethodAt(t, k).name, carried));
        }
        gReg.addImplAs(concrete, tr, fns, carried);
    }

    // `f(x)` where f is a fn-typed variable: the callee is what the variable holds.
    lowerFnPtrCall &self inout a:Ast id:NodeId c:long -> Temp {
        e: Expr = a.expr(id);
        cn: CallNode = a.calls.get(c);
        // The callee: an expression when the thing being called is a struct field, and the named
        // variable otherwise. Both yield the address to call through.
        fn: Temp = NO_TEMP;
        if (cn.callee != NO_NODE) { fn = self.lowerExpr(a, cn.callee); }
        else {
            fn = self.ir.newTemp(Lit.Ptr, NO_SYM);
            ld: Instr = instr(IROp.Load);
            ld.dst = fn; ld.name = cn.name; ld.kind = Lit.Ptr;
            ld.isGlobal = self.ir.isGlobalName(cn.name);
            self.ir.emit(ld);
        }

        argTemps: Vec<Temp>;
        for k in 0..cn.argCount { argTemps.push(self.lowerArg(a, a.argAt(cn, k))); }

        ret: Temp = NO_TEMP;
        if (returnedByPointer(e.kind, e.structName)) {
            slot: long = self.ir.addAggSlot(aggregateBytes(e.kind, e.structName));
            ret = self.ir.newTemp(Lit.Ptr, e.structName);
            sl: Instr = instr(IROp.AggSlot);
            sl.dst = ret; sl.imm = slot; sl.kind = Lit.Ptr;
            self.ir.emit(sl);
        }
        first: long = self.ir.args.len();
        if (ret != NO_TEMP) { self.ir.args.push(ret); }
        self.ir.args.extend(argTemps);

        t: Temp = NO_TEMP;
        if (returnedByPointer(e.kind, e.structName)) { t = ret; }
        else if (e.kind != Lit.Void) { t = self.ir.newTemp(e.kind, e.structName); }
        in: Instr = instr(IROp.CallIndirect);
        in.dst = t; in.a = fn;
        in.firstArg = first;
        in.argCount = self.ir.args.len() - first;
        in.kind = e.kind;
        self.ir.emit(in);
        return t;
    }

    // A `...T` tail, recorded before anything is lowered.
    noteVariadic &self inout a:Ast f:FnNode -> void {
        if (f.argCount == 0) { return; }
        last: VarDeclNode = a.paramAt(f, f.argCount - 1);
        if (!last.isVariadic) { return; }
        self.varSigs.push(VarSig { fixed: f.argCount - 1, elemKind: last.elemKind,
                                   elemStruct: last.elemStruct });
        self.variadics.put(nameOf(f.name), self.varSigs.len() - 1);
    }

    // A startup or shutdown hook, by its declaration (`@init`/`@fini`): `_start` calls them
    // (`asm.k`), in the order the modules were read.
    noteHook &self f:FnNode -> void {
        if ((f.attrs & FN_INIT) != 0) { gInitHooks.push(f.name); return; }
        if ((f.attrs & FN_FINI) != 0) { gFiniHooks.push(f.name); }
    }

    // A call to a `builtin`: the primitive itself, in place of a call.
    //
    //   syscall(nr, a, b, ...)  the `syscall` instruction, System V's syscall convention: the
    //                           number in rax, the arguments in rdi, rsi, rdx, r10, r8, r9, the
    //                           result in rax (an `asm` block, so the allocator treats it as the
    //                           clobber it is)
    //   atCompileTime()         false: the program is running, and the branch it guards is dead
    //   exit(status)            the `@fini` hooks (`__kiln_fini`), then exit_group
    //   parseExpr(src)          a trap: the parser exists only while the compiler runs
    lowerBuiltin &self inout a:Ast id:NodeId cn:CallNode bk:long -> Temp {
        e: Expr = a.expr(id);
        if (bk == BI_AT_COMPILE_TIME) { return self.constTemp(0, Lit.Bool); }
        if (bk == BI_SYSCALL) {
            if (cn.argCount > 7) { failStr(stringOf("a syscall takes a number and at most six arguments")); }
            first: long = self.ir.asmKinds.len();
            regs: [str; 7] = ["rax", "rdi", "rsi", "rdx", "r10", "r8", "r9"];
            vals: Vec<Temp>;
            for k in 0..cn.argCount { vals.push(self.lowerExpr(a, a.argAt(cn, k))); }
            for k in 0..cn.argCount {
                self.ir.addAsmPiece(AsmKind.In, intern(regs[k]), NO_SYM, vals.get(k), NO_SYM, 8);
            }
            self.ir.addAsmPiece(AsmKind.Text, NO_SYM, NO_SYM, NO_TEMP, intern("syscall"), 8);
            slot: Sym = internString(format("$sysret{}", self.asmSeq));
            self.asmSeq = self.asmSeq + 1;
            self.ir.addAsmPiece(AsmKind.Out, intern("rax"), slot, NO_TEMP, NO_SYM, 8);
            in: Instr = instr(IROp.Asm);
            in.firstPiece = first;
            in.pieceCount = self.ir.asmKinds.len() - first;
            self.ir.emit(in);
            ld: Instr = instr(IROp.Load);
            ld.dst = self.ir.newTemp(Lit.Long, NO_SYM);
            ld.name = slot;
            ld.kind = Lit.Long;
            self.ir.emit(ld);
            return ld.dst;
        }
        if (bk == BI_EXIT) {
            gUsesFini = true;
            st: Temp = self.lowerExpr(a, a.argAt(cn, 0));
            first: long = self.ir.asmKinds.len();
            self.ir.addAsmPiece(AsmKind.In, intern("rdi"), NO_SYM, st, NO_SYM, 8);
            // r12 is callee-saved, so the hooks keep the status for the exit; nothing after this
            // needs the register back.
            self.ir.addAsmPiece(AsmKind.Text, NO_SYM, NO_SYM, NO_TEMP, intern("mov r12, rdi"), 8);
            self.ir.addAsmPiece(AsmKind.Text, NO_SYM, NO_SYM, NO_TEMP, intern("call __kiln_fini"), 8);
            self.ir.addAsmPiece(AsmKind.Text, NO_SYM, NO_SYM, NO_TEMP, intern("mov rdi, r12"), 8);
            self.ir.addAsmPiece(AsmKind.Text, NO_SYM, NO_SYM, NO_TEMP, intern("mov rax, 231"), 8);
            self.ir.addAsmPiece(AsmKind.Text, NO_SYM, NO_SYM, NO_TEMP, intern("syscall"), 8);
            in: Instr = instr(IROp.Asm);
            in.firstPiece = first;
            in.pieceCount = self.ir.asmKinds.len() - first;
            self.ir.emit(in);
            return NO_TEMP;
        }
        // BI_PARSE_EXPR: a trap where it is reached, and a result slot nothing reads.
        first: long = self.ir.asmKinds.len();
        self.ir.addAsmPiece(AsmKind.Text, NO_SYM, NO_SYM, NO_TEMP, intern("ud2"), 8);
        in: Instr = instr(IROp.Asm);
        in.firstPiece = first;
        in.pieceCount = 1;
        self.ir.emit(in);
        if (!returnedByPointer(e.kind, e.structName)) { return self.constTemp(0, e.kind); }
        slot: long = self.ir.addAggSlot(aggregateBytes(e.kind, e.structName));
        ret: Temp = self.ir.newTemp(Lit.Ptr, e.structName);
        sl: Instr = instr(IROp.AggSlot);
        sl.dst = ret;
        sl.imm = slot;
        sl.kind = Lit.Ptr;
        self.ir.emit(sl);
        return ret;
    }

    variadicOf &self n:Sym -> long {
        hit: Option<long> = self.variadics.find(nameOf(n));
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }

    // A hidden scratch block in this frame, and the temp holding its address.
    aggSlotFor &self bytes:long -> Temp {
        slot: long = self.ir.addAggSlot(bytes);
        t: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
        sl: Instr = instr(IROp.AggSlot);
        sl.dst = t; sl.imm = slot; sl.kind = Lit.Ptr;
        self.ir.emit(sl);
        return t;
    }

    storeAt &self base:Temp off:long v:Temp k:Lit -> void {
        st: Instr = instr(IROp.PtrStore);
        st.a = base; st.b = v; st.imm = off; st.kind = k;
        self.ir.emit(st);
    }

    // `base + off` as an address in its own right, for a block copy into part of a slot.
    offsetPtr &self base:Temp off:long -> Temp {
        if (off == 0) { return base; }
        t: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
        in: Instr = instr(IROp.Add);
        in.dst = t; in.a = base; in.b = self.constTemp(off, Lit.Long); in.kind = Lit.Ptr;
        self.ir.emit(in);
        return t;
    }

    // Build a `...T` tail: the trailing arguments into a stack element-array, then the 16-byte
    // {ptr, len} header that is the callee's slice parameter. An empty tail still gets a valid
    // slot, so the callee's `len == 0` loop reads a real address and not a stale register.
    buildVariadicSlice &self inout a:Ast nodes:Vec<NodeId> sig:VarSig -> Temp {
        count: long = nodes.len() - sig.fixed;
        if (count < 0) { count = 0; }
        // `...Tok` is a tail of integers, however the type is spelled: a backed enum reaches here
        // as `Lit.Struct` with a name the struct registry has never heard of, and `structBytes`
        // answered 0 for it: a zero stride writes every argument over the first one.
        ek: Lit = storedKind(sig.elemKind, sig.elemStruct);
        elem: long = typeInfo(ek).size;
        if (ek == Lit.Struct) { elem = structBytes(sig.elemStruct); }
        if (elem < 1) { elem = 8; }
        bytes: long = count * elem;
        if (bytes < 8) { bytes = 8; }
        arr: Temp = self.aggSlotFor(bytes);

        for k in 0..count {
            arg: NodeId = nodes.get(sig.fixed + k);
            off: long = k * elem;
            if (ek == Lit.Any) { self.boxAny(a, arr, off, arg); }
            else if (isAggregate(ek)) {
                src: Temp = self.placeOf(a, arg);
                self.copyInto(self.offsetPtr(arr, off), src, elem);
            } else {
                self.storeAt(arr, off, self.lowerExpr(a, arg), ek);
            }
        }

        hdr: Temp = self.aggSlotFor(16);
        self.storeAt(hdr, 0, arr, Lit.Ptr);
        self.storeAt(hdr, 8, self.constTemp(count, Lit.Long), Lit.Long);
        return hdr;
    }

    // One `any`: 24 bytes of {tag, x, y}, matching `stdlib/fmt.k`'s `AnyBox` and `BoxTag`. The
    // tag says how to read the other two words, and is chosen by width and signedness rather
    // than by naming a type -- an 8-byte value tagged as an int has its top half read as absent.
    boxAny &self inout a:Ast base:Temp off:long arg:NodeId -> void {
        e: Expr = a.expr(arg);
        isObj: bool = e.kind == Lit.TraitObj && lastComponentOf(nameOf(e.structName)) == "Display";
        isVal: bool = (e.kind == Lit.Struct || e.kind == Lit.Ref)
                      && e.structName != NO_SYM
                      && gReg.structImplements(nameOf(e.structName), intern("Display"));
        if (isVal || isObj) {
            // Boxed as a Display trait object: the value's address and the table its `display`
            // is found in. A concrete struct is coerced here; a `Display` already is one, so its
            // two halves are unpacked rather than rebuilt.
            data: Temp = NO_TEMP;
            vt: Temp = NO_TEMP;
            if (isVal && namedScalar(e.kind, e.structName)) {
                // A backed enum or a distinct type: a borrow of one is the integer it is (`&self`
                // of a named scalar receives the value, `refToScalar`), so the value is the data.
                data = self.lowerExpr(a, arg);
                vt = self.ir.newTemp(Lit.Ptr, NO_SYM);
                va: Instr = instr(IROp.VtableAddr);
                va.dst = vt; va.name = intern(vtableName(e.structName, intern("Display")));
                va.kind = Lit.Ptr;
                self.ir.emit(va);
            } else if (isVal) {
                data = self.baseAddress(a, arg);
                vt = self.ir.newTemp(Lit.Ptr, NO_SYM);
                va: Instr = instr(IROp.VtableAddr);
                va.dst = vt; va.name = intern(vtableName(e.structName, intern("Display")));
                va.kind = Lit.Ptr;
                self.ir.emit(va);
            } else {
                obj: Temp = self.lowerAddress(a, arg);
                data = self.loadWord(obj, 0);
                vt = self.loadWord(obj, 8);
            }
            self.storeAt(base, off, self.constTemp(3, Lit.Long), Lit.Long);
            self.storeAt(base, off + 8, data, Lit.Ptr);
            self.storeAt(base, off + 16, vt, Lit.Ptr);
            return;
        }
        if (e.kind == Lit.Str) {
            src: Temp = self.placeOf(a, arg);
            self.storeAt(base, off, self.constTemp(2, Lit.Long), Lit.Long);
            self.storeAt(base, off + 8, self.loadWord(src, 0), Lit.Ptr);
            self.storeAt(base, off + 16, self.loadWord(src, 8), Lit.Long);
            return;
        }
        tag: long = 0;                                     // int
        if (e.kind == Lit.Char) { tag = 4; }
        else if (e.kind == Lit.Long) { tag = 1; }
        else if (e.kind == Lit.U64 || e.kind == Lit.Ptr) { tag = 5; }
        else if (e.kind == Lit.Double) { tag = 6; }       // the f64's bits
        else if (e.kind == Lit.Float) { tag = 7; }        // the f32's, sign-extended
        else if (isTruthValue(e.kind, e.op)) { tag = boxTagOf("Bool", 0); }
        self.storeAt(base, off, self.constTemp(tag, Lit.Long), Lit.Long);
        self.storeAt(base, off + 8, self.lowerExpr(a, arg), Lit.Long);
        // A float's box carries the formatter's address, which is what makes a program that
        // formats a float -- and only one -- reach it (`gFloatBoxFormat`).
        if ((tag == 6 || tag == 7) && gFloatBoxFormat != NO_SYM) {
            fp: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
            fa: Instr = instr(IROp.FnAddr);
            fa.dst = fp; fa.name = gFloatBoxFormat; fa.kind = Lit.Ptr;
            self.ir.emit(fa);
            self.storeAt(base, off + 16, fp, Lit.Ptr);
        }
    }

    loadWord &self base:Temp off:long -> Temp {
        t: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
        ld: Instr = instr(IROp.PtrLoad);
        ld.dst = t; ld.a = base; ld.imm = off; ld.kind = Lit.Ptr;
        self.ir.emit(ld);
        return t;
    }

    // `p + n`, `n + p`, `p - n` and `q - p` where p is a `*T`. NO_TEMP when this is not one of
    // those, so the ordinary binary path handles everything else unchanged: with the operands
    // already lowered, because what makes an expression pointer arithmetic is a fact about the
    // temps, not about the syntax tree.
    //
    // The pointee comes from `ir.pointeeOf`, the tracked fact, never from the static type of the
    // node. The two disagree exactly where it matters: `s.ptr` on a `str` is a `Lit.Ptr`
    // expression whose companion name is empty (a `str` names no element type), and reading a
    // width off that name answered 8, so `strSlice(s, 7, n)` and `strCmp`'s `s.ptr + i` walked
    // eight bytes an index and landed in some other string entirely. An untracked pointer is a
    // raw address, exactly as a `&x` long is, and a raw address is not scaled.
    lowerPtrArith &self inout a:Ast id:NodeId l:Temp r:Temp -> Temp {
        e: Expr = a.expr(id);
        if (e.op != Op.Addition && e.op != Op.Subtraction) { return NO_TEMP; }
        lp: Sym = self.ir.pointeeOf(l);
        rp: Sym = self.ir.pointeeOf(r);
        if (lp == NO_SYM && rp == NO_SYM) { return NO_TEMP; }

        // Two pointers into the same block subtract to an element count.
        if (lp != NO_SYM && rp != NO_SYM && e.op == Op.Subtraction) {
            pw: long = namedWidth(lp);
            d: Temp = self.arith(IROp.Sub, l, r, Lit.Long);
            if (pw == 1) { return d; }
            return self.arith(IROp.Div, d, self.constTemp(pw, Lit.Long), Lit.Long);
        }
        // `n + p` is `p + n`. Only addition may be written that way round; `n - p` is not an
        // address, and nothing in the language spells one.
        base: Temp = l;
        other: Temp = r;
        pn: Sym = lp;
        if (lp == NO_SYM) { base = r; other = l; pn = rp; }
        w: long = namedWidth(pn);
        step: Temp = other;
        if (w != 1) { step = self.arith(IROp.Mul, other, self.constTemp(w, Lit.Long), Lit.Long); }
        out: Temp = self.arith(opFor(e.op), base, step, Lit.Ptr);
        self.ir.notePointee(out, pn);   // the answer points at whatever the base did
        return out;
    }

    lowerCall &self inout a:Ast id:NodeId c:long -> Temp {
        e: Expr = a.expr(id);
        cn: CallNode = a.calls.get(c);
        if (cn.slot == SLOT_FNPTR) { return self.lowerFnPtrCall(a, id, c); }
        if (cn.slot != NO_SLOT) { return self.lowerDispatch(a, id, c); }
        if (cn.receiver == NO_NODE && !self.builtinKinds.isEmpty()) {
            hit: Option<long> = self.builtinKinds.find(nameOf(cn.name));
            match hit { Some(bk) { return self.lowerBuiltin(a, id, cn, bk); } None { } }
        }
        argTemps: Vec<Temp>;
        nodes: Vec<NodeId>;
        if (cn.receiver != NO_NODE) { nodes.push(cn.receiver); }
        k: long = 0;
        while (k < cn.argCount) { nodes.push(a.argAt(cn, k)); k = k + 1; }

        vs: long = self.variadicOf(cn.name);
        if (vs == NOT_FOUND) {
            k = 0;
            while (k < nodes.len()) { argTemps.push(self.lowerArg(a, nodes.get(k))); k = k + 1; }
        } else {
            sig: VarSig = self.varSigs.get(vs);
            k = 0;
            while (k < sig.fixed && k < nodes.len()) {
                argTemps.push(self.lowerArg(a, nodes.get(k)));
                k = k + 1;
            }
            argTemps.push(self.buildVariadicSlice(a, nodes, sig));
        }

        // An aggregate result needs somewhere to live: a scratch slot in this frame, whose
        // address goes in front of the real arguments.
        ret: Temp = NO_TEMP;
        if (returnedByPointer(e.kind, e.structName)) {
            slot: long = self.ir.addAggSlot(aggregateBytes(e.kind, e.structName));
            ret = self.ir.newTemp(Lit.Ptr, e.structName);
            sl: Instr = instr(IROp.AggSlot);
            sl.dst = ret;
            sl.imm = slot;
            sl.kind = Lit.Ptr;
            self.ir.emit(sl);
        }

        first: long = self.ir.args.len();
        if (ret != NO_TEMP) { self.ir.args.push(ret); }
        self.ir.args.extend(argTemps);

        t: Temp = NO_TEMP;
        if (returnedByPointer(e.kind, e.structName)) { t = ret; }
        else if (e.kind != Lit.Void) { t = self.ir.newTemp(e.kind, e.structName); }
        in: Instr = instr(IROp.Call);
        in.dst = t;
        in.name = cn.name;
        in.firstArg = first;
        in.argCount = self.ir.args.len() - first;
        in.kind = e.kind;
        in.noReturn = gNoReturnFns.has(nameOf(cn.name));
        // The result already sits in the slot the hidden pointer named, so the call writes no
        // destination temp of its own.
        if (returnedByPointer(e.kind, e.structName)) { in.dst = NO_TEMP; }
        self.ir.emit(in);
        return t;
    }
}

pub sretSym -> Sym { return intern("$sret"); }

// How many bytes a named aggregate occupies.
pub structBytes n:Sym -> long {
    if (n == NO_SYM) { return 8; }
    at: long = gReg.findStruct(nameOf(n));
    if (at < 0) { return 8; }
    b: long = gReg.structDef(at).size;
    if (b < 8) { b = 8; }
    return b;
}

// Which types travel as a pointer rather than in a register. A struct is too big for one, and a
// `Ref` (which is what a `&self` receiver and an `inout` parameter become) is a pointer already.
// `str` and a slice are a pointer to their pair, so they arrive as one without anything extra.
// A trait object is sixteen bytes of {data, vtable} and travels exactly as a struct does, which
// is what makes its parameter slot hold an address, so reading it is a load and not an `lea`.
//
// It takes the companion name as well as the kind, because a kind alone cannot answer: the parser
// gives every named type it does not otherwise recognise `Lit.Struct`, and a backed enum is one of
// those. `config: BufWriterConfig` is an integer, and copying sixteen bytes from the integer 1 as
// though it were an address is what it did before this asked.
pub passedByPointer k:Lit n:Sym -> bool {
    if (namedScalar(k, n)) { return false; }
    return isAggregate(k) || k == Lit.Ref;
}

// Whether a value of this type lives inline where it is stored: in a struct field, a local's
// slot, a global, an array element. An aggregate does. A ref does not: it is an eight-byte
// pointer to one, so a `&S` field holds an address, writing it is a word store rather than a
// block copy, and reading it is a load rather than the field's own address.
//
// `passedByPointer` cannot answer this. It says how a value travels to a callee, and a borrow
// travels the way an aggregate does precisely because both arrive as an address, which is why
// the two questions read alike, and why conflating them was silent: a closure's captured `&S`
// field was filled by copying the first eight bytes of the borrowed struct over the pointer, so
// `a.bump(5)` inside the closure wrote to the closure and `a.n` read the struct's first word
// whichever field was asked for.
pub storedInline k:Lit n:Sym -> bool {
    if (k == Lit.Ref) { return false; }
    return passedByPointer(k, n);
}

// What a return, and so a call's result, travels as. A `-> &T` hands back an address, which is one
// register, so it comes back like a scalar even though `&T` borrows an aggregate, and only a
// value with no register to fit in needs the hidden result pointer. Routing a borrow through that
// pointer copied the first eight bytes of the borrowed object where its address should have gone.
pub returnedByPointer k:Lit n:Sym -> bool {
    if (k == Lit.Ref) { return false; }
    return passedByPointer(k, n);
}

// The bytes a value of this type occupies where it lives. A `str` or a slice is its two words, a
// trait object its {data, vtable}, an `any` its tagged three; only a named aggregate has to ask
// the registry. Reading this off `structBytes` alone answered 8 for every one of them, which is
// how a slice local came to hold half a fat pointer.
pub aggregateBytes k:Lit n:Sym -> long {
    if (namedScalar(k, n)) { return 8; }    // one register, like any other integer
    if (k == Lit.Struct || k == Lit.Tuple) { return structBytes(n); }
    b: long = typeInfo(k).size;
    if (b < 8) { b = 8; }
    return b;
}

// The storage a declaration needs: an array is its element width times its count, a struct is its
// declared size, and everything else fits in one register.
pub declaredBytes d:VarDeclNode -> long {
    unit: long = typeInfo(d.kind).size;
    // A backed enum first, so `xs: [Tok; 128]` strides by the backing integer the way an indexing
    // expression's `typeBytes` does, the two are the same array and must agree on its shape.
    if (namedScalar(d.kind, d.structName)) { unit = typeInfo(namedScalarBacking(d.structName)).size; }
    else if (d.kind == Lit.Struct && d.structName != NO_SYM) {
        at: long = gReg.findStruct(nameOf(d.structName));
        if (at >= 0) { unit = gReg.structDef(at).size; }
    }
    if (unit < 1) { unit = 8; }
    if (d.isArray) { return unit * d.count; }
    if (unit < 8) { return 8; }
    return unit;
}

// The type both operands of an operation widen to: the higher-ranked of the two, and never
// narrower than `int`, which is where the numeric ladder starts. A type off the ladder (an
// aggregate, an address) does not widen at all and keeps the left operand's type, which is what
// the back end then sizes by.
pub commonKind x:Lit y:Lit -> Lit {
    if (typeInfo(x).precedence == 0 || typeInfo(y).precedence == 0) { return x; }
    c: Lit = x;
    if (typeInfo(y).precedence > typeInfo(x).precedence) { c = y; }
    if (typeInfo(c).size < typeInfo(Lit.Int).size) { return Lit.Int; }
    return c;
}

// The IR operation a syntax operator lowers to, as a table built once and indexed by the
// operator rather than walked as a chain of comparisons. `Mov` for anything with no arithmetic of
// its own: every such operator is handled before this is asked.
local gOpFor: Vec<IROp> = opTable();

pub opFor op:Op -> IROp { return gOpFor.get(op as long); }

local opTable -> Vec<IROp> {
    gOpFor: Vec<IROp>;
    {
        i: long = 0;
        while (i <= (Op.MakeTraitObj as long)) { gOpFor.push(IROp.Mov); i = i + 1; }
        gOpFor.set(Op.Addition as long,         IROp.Add);
        gOpFor.set(Op.Subtraction as long,      IROp.Sub);
        gOpFor.set(Op.Multiplication as long,   IROp.Mul);
        gOpFor.set(Op.Division as long,         IROp.Div);
        gOpFor.set(Op.Modulus as long,          IROp.Mod);
        gOpFor.set(Op.BitwiseAnd as long,       IROp.BAnd);
        gOpFor.set(Op.BitwiseOr as long,        IROp.BOr);
        gOpFor.set(Op.BitwiseXor as long,       IROp.BXor);
        gOpFor.set(Op.ShiftLeft as long,        IROp.Shl);
        gOpFor.set(Op.ShiftRight as long,       IROp.Shr);
        gOpFor.set(Op.IsEqual as long,          IROp.CmpEq);
        gOpFor.set(Op.IsNotEqual as long,       IROp.CmpNe);
        gOpFor.set(Op.LessThan as long,         IROp.CmpLt);
        gOpFor.set(Op.GreaterThan as long,      IROp.CmpGt);
        gOpFor.set(Op.IsLessOrEqual as long,    IROp.CmpLe);
        gOpFor.set(Op.IsGreaterOrEqual as long, IROp.CmpGe);
    }
    return gOpFor;
}

pub nameEndsWith s:str suffix:str -> bool { return strEndsWith(s, suffix); }

// ─── an array written in full before it is read ───────────────────────────────
//
// Statement `k` of block `b` declares a local array without a value, and what follows plainly
// writes every element before anything reads the array: one store per element by constant index
// (what `xs: [T; N] = [a, b, ...]` is written out as), or a range loop over exactly `0..N` whose
// body begins with `xs[i] = v` and holds no `break` and no write to `i`, where no stored value
// reads `xs`. Plainly: anything else keeps the fill.
local writtenInFull inout a:Ast b:long k:long -> bool {
    d: VarDeclNode = a.decls.get(a.stmtAt(b, k).at);
    if (!d.isArray || d.init != NO_NODE || d.count <= 0) { return false; }
    n: long = a.blockLen(b);
    // One store per element.
    if (k + d.count < n) {
        seen: Vec<bool>;
        for j in 0..d.count { seen.push(false); }
        all: bool = true;
        for j in 0..d.count {
            v: long = constStoreIndex(a, a.stmtAt(b, k + 1 + j), d.name);
            if (v < 0 || v >= d.count || seen.get(v)) { all = false; break; }
            seen.set(v, true);
        }
        if (all) { return true; }
    }
    // A range loop: `{ i: long = 0; while (i < N) { xs[i] = v; ... } step { i = i + 1; } }`.
    if (k + 1 >= n) { return false; }
    st: Stmt = a.stmtAt(b, k + 1);
    if (st.kind != StmtKind.Block) { return false; }
    lb: long = a.blockStmts.get(st.at).body;
    if (a.blockLen(lb) != 2) { return false; }
    s0: Stmt = a.stmtAt(lb, 0);
    s1: Stmt = a.stmtAt(lb, 1);
    if (s0.kind != StmtKind.VarDecl || s1.kind != StmtKind.While) { return false; }
    iv: VarDeclNode = a.decls.get(s0.at);
    if (iv.init == NO_NODE || litValue(a, iv.init) != 0) { return false; }
    w: WhileNode = a.whiles.get(s1.at);
    c: Expr = a.expr(w.cond);
    if (c.op != Op.LessThan || nameIn(a, c.left) != iv.name || litValue(a, c.right) != d.count) { return false; }
    if (w.step < 0 || a.blockLen(w.body) == 0) { return false; }
    first: Stmt = a.stmtAt(w.body, 0);
    if (first.kind != StmtKind.Expr) { return false; }
    e: Expr = a.expr(a.exprStmts.get(first.at).value);
    if (e.op != Op.Assignment || mentions(a, e.right, d.name)) { return false; }
    l: Expr = a.expr(e.left);
    lp: Payload = l.payload;
    match lp {
        Index(x) {
            ix: IndexNode = a.indexes.get(x);
            if (ix.whole || nameIn(a, ix.base) != d.name || nameIn(a, ix.index) != iv.name) { return false; }
        }
        _ { return false; }
    }
    return !breaksOrWrites(a, w.body, iv.name);
}

// `xs[j] = v` with `j` a constant and `v` not reading `xs`: `j`, or -1.
local constStoreIndex inout a:Ast st:Stmt xs:Sym -> long {
    if (st.kind != StmtKind.Expr) { return -1; }
    e: Expr = a.expr(a.exprStmts.get(st.at).value);
    if (e.op != Op.Assignment || mentions(a, e.right, xs)) { return -1; }
    l: Expr = a.expr(e.left);
    lp: Payload = l.payload;
    match lp {
        Index(x) {
            ix: IndexNode = a.indexes.get(x);
            if (ix.whole || nameIn(a, ix.base) != xs) { return -1; }
            return litValue(a, ix.index);
        }
        _ { }
    }
    return -1;
}

// The name a bare variable reference names, or NO_SYM.
local nameIn inout a:Ast id:NodeId -> Sym {
    if (id == NO_NODE) { return NO_SYM; }
    e: Expr = a.expr(id);
    if (e.op != Op.Lvalue) { return NO_SYM; }
    p: Payload = e.payload;
    match p { Name(n) { return n; } _ { } }
    return NO_SYM;
}

// An integer literal's value, or -1.
local litValue inout a:Ast id:NodeId -> long {
    if (id == NO_NODE) { return -1; }
    e: Expr = a.expr(id);
    if (e.op != Op.Literal) { return -1; }
    p: Payload = e.payload;
    match p { Num(v) { return v; } _ { } }
    return -1;
}

// Whether an expression names `n` anywhere in it.
local mentions inout a:Ast id:NodeId n:Sym -> bool {
    if (id == NO_NODE) { return false; }
    e: Expr = a.expr(id);
    if (e.left != NO_NODE || e.right != NO_NODE) { return mentions(a, e.left, n) || mentions(a, e.right, n); }
    p: Payload = e.payload;
    match p {
        Name(x) { return x == n; }
        Sub(v) { return mentions(a, v, n); }
        Field(f) { return mentions(a, a.fields.get(f).base, n); }
        Index(i) {
            ix: IndexNode = a.indexes.get(i);
            return mentions(a, ix.base, n) || mentions(a, ix.index, n)
                || mentions(a, ix.sliceStart, n) || mentions(a, ix.sliceEnd, n);
        }
        Call(c) {
            cn: CallNode = a.calls.get(c);
            if (mentions(a, cn.receiver, n) || mentions(a, cn.callee, n)) { return true; }
            for k in 0..cn.argCount { if (mentions(a, a.argAt(cn, k), n)) { return true; } }
            return false;
        }
        Lit(l) {
            ln: LitNode = a.lits.get(l);
            for k in 0..ln.initCount { if (mentions(a, a.inits.get(ln.firstInit + k).value, n)) { return true; } }
            return mentions(a, ln.rest, n);
        }
        _ { }
    }
    return false;
}

// Whether a loop body may leave early (`break`, or anything but a plain statement we can read) or
// write its counter `i`.
local breaksOrWrites inout a:Ast b:long i:Sym -> bool {
    if (b < 0) { return false; }
    for k in 0..a.blockLen(b) {
        st: Stmt = a.stmtAt(b, k);
        if (st.kind == StmtKind.Break || st.kind == StmtKind.Asm || st.kind == StmtKind.With) { return true; }
        if (st.kind == StmtKind.Expr) {
            e: Expr = a.expr(a.exprStmts.get(st.at).value);
            if (e.op == Op.Assignment && nameIn(a, e.left) == i) { return true; }
            if (mentionsAddressOf(a, a.exprStmts.get(st.at).value, i)) { return true; }
        }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                if (breaksOrWrites(a, br.body, i)) { return true; }
                at = br.elseIf;
            }
        }
        if (st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
            if (breaksOrWrites(a, a.blockStmts.get(st.at).body, i)) { return true; }
        }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for j in 0..m.armCount { if (breaksOrWrites(a, a.arms.get(m.firstArm + j).body, i)) { return true; } }
        }
        // A nested loop's own `break` leaves only it; a write to `i` inside it still counts.
        if (st.kind == StmtKind.While || st.kind == StmtKind.Loop) {
            inner: long = -1;
            if (st.kind == StmtKind.While) { inner = a.whiles.get(st.at).body; } else { inner = a.blockStmts.get(st.at).body; }
            if (writesCounter(a, inner, i)) { return true; }
        }
    }
    return false;
}
local writesCounter inout a:Ast b:long i:Sym -> bool {
    if (b < 0) { return false; }
    for k in 0..a.blockLen(b) {
        st: Stmt = a.stmtAt(b, k);
        if (st.kind == StmtKind.Expr) {
            e: Expr = a.expr(a.exprStmts.get(st.at).value);
            if (e.op == Op.Assignment && nameIn(a, e.left) == i) { return true; }
            if (mentionsAddressOf(a, a.exprStmts.get(st.at).value, i)) { return true; }
        }
        if (st.kind == StmtKind.Asm) { return true; }
    }
    return false;
}
// `&i` anywhere in an expression: the counter lent, and so perhaps written.
local mentionsAddressOf inout a:Ast id:NodeId i:Sym -> bool {
    if (id == NO_NODE) { return false; }
    e: Expr = a.expr(id);
    if (e.op == Op.AddressOf) {
        p: Payload = e.payload;
        match p { Sub(v) { if (nameIn(a, v) == i) { return true; } } _ { } }
    }
    if (e.left != NO_NODE || e.right != NO_NODE) { return mentionsAddressOf(a, e.left, i) || mentionsAddressOf(a, e.right, i); }
    p2: Payload = e.payload;
    match p2 {
        Call(c) {
            cn: CallNode = a.calls.get(c);
            for k in 0..cn.argCount { if (mentionsAddressOf(a, a.argAt(cn, k), i)) { return true; } }
            return mentionsAddressOf(a, cn.receiver, i);
        }
        Sub(v) { return mentionsAddressOf(a, v, i); }
        _ { }
    }
    return false;
}

methods Lowerer {
    // ─── aggregates ──────────────────────────────────────────────────────────
    //
    // A value larger than a register lives in memory and flows as a pointer. A struct local is a
    // block in the frame; reading a field is a load through the block's address at the field's
    // offset, and writing one is the store. That is the whole of it: the offsets were computed
    // when the struct was declared, so nothing here has to know a struct's shape.

    isByRef &self name:Sym -> bool { return self.byRef.has(nameOf(name)); }
    noteByRef &self name:Sym -> void { self.byRef.put(nameOf(name), 1); }

    // How long the fixed array `name` is, or NOT_FOUND when it is not one.
    arrayCount &self name:Sym -> long {
        hit: Option<long> = self.arrayLen.find(nameOf(name));
        match hit { Some(n) { return n; } None { } }
        // A global array: its count is the declaration's. Without it `G[..]` was a slice of
        // length zero, so `for x in G` walked nothing, and `G[i]` was not bounds-checked.
        gi: long = gReg.findGlobal(nameOf(name));
        if (gi >= 0 && gReg.globalDef(gi).isArray) { return gReg.globalDef(gi).count; }
        return NOT_FOUND;
    }

    // The address of a named variable's storage. For a by-pointer parameter the slot holds the
    // address, so the address of the value is a load of the slot, not the slot's own address.
    addressOfVar &self name:Sym pointee:Sym -> Temp {
        if (self.isByRef(name)) {
            t: Temp = self.ir.newTemp(Lit.Ptr, pointee);
            ld: Instr = instr(IROp.Load);
            ld.dst = t;
            ld.name = name;
            ld.kind = Lit.Ptr;
            self.ir.emit(ld);
            self.ir.notePointee(t, pointee);
            return t;
        }
        t: Temp = self.ir.newTemp(Lit.Ptr, pointee);
        in: Instr = instr(IROp.AddrOf);
        in.dst = t;
        in.name = name;
        in.kind = Lit.Ptr;
        in.structName = pointee;
        in.isGlobal = self.ir.isGlobalName(name);
        self.ir.emit(in);
        self.ir.notePointee(t, pointee);
        return t;
    }

    // The address of the aggregate an expression denotes, rather than its value. A field chain
    // walks down through offsets without ever materialising the intermediate structs.
    // The operand of a prefix node: `&x`, `*p`, `!b`, a cast. It rides in the payload as a
    // sub-expression, which is the one shape all of them share.
    subNode &self inout a:Ast id:NodeId -> NodeId {
        p: Payload = a.expr(id).payload;
        match p { Sub(inner) { return inner; } _ { } }
        return NO_NODE;
    }

    lowerAddress &self inout a:Ast id:NodeId -> Temp {
        if (id == NO_NODE) { return NO_TEMP; }
        e: Expr = a.expr(id);
        // The place `*p` names is `p`. Without this a `-> &T` returning one fell through to the
        // value path and handed back what `p` pointed at instead of `p`.
        if (e.op == Op.Deref) { return self.lowerExpr(a, self.subNode(a, id)); }
        p: Payload = e.payload;
        match p {
            Name(n) { return self.addressOfVar(n, e.structName); }
            Call(_) { return self.lowerExpr(a, id); }   // the call already wrote into a slot
            Lit(_)  { return self.lowerExpr(a, id); }   // and so did the literal
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                // A slice expression is a fresh fat pointer, and its value is the address of
                // that pair, so `&b[used..]` is the new header, not the bytes it points at.
                if (ix.whole || ix.sliceStart != NO_NODE || ix.sliceEnd != NO_NODE) {
                    return self.lowerSliceOf(a, ix, self.baseElemWidth(a, ix.base));
                }
                // `cs[1].a`: the element's address is the base a field offset applies to, which
                // is why indexing has to answer here and not only as a value.
                fd: FieldDef = self.fieldArrayDef(a, ix.base);
                if (fd.name != NO_SYM) { return self.lowerElemAddress(a, ix, typeBytes(fd.kind, fd.structName)); }
                return self.lowerElemAddress(a, ix, self.elemWidth(a, id));
            }
            Field(f) {
                fn: FieldNode = a.fields.get(f);
                base: Temp = self.baseAddress(a, fn.base);
                if (base == NO_TEMP) { return NO_TEMP; }
                off: long = self.fieldOffset(a, fn.base, fn.name);
                if (off == 0) { return base; }
                t: Temp = self.ir.newTemp(Lit.Ptr, e.structName);
                k: Temp = self.constTemp(off, Lit.Long);
                in: Instr = instr(IROp.Add);
                in.dst = t;
                in.a = base;
                in.b = k;
                in.kind = Lit.Long;
                self.ir.emit(in);
                return t;
            }
            _ { }
        }
        return NO_TEMP;
    }

    // The address of the aggregate a field is read out of. A `*T` holds that address, so the base
    // is the pointer's value; taking the address of the pointer's own slot instead read the
    // pointer where the struct should be, and `e.tag` answered with `e`. A ref is the same
    // arrangement under a different name (a borrow is the address) and for one held in a field
    // (a closure's captured `&S`) the difference is exactly the load that makes `__cl.a.n` reach
    // the borrowed struct instead of the closure.
    baseAddress &self inout a:Ast id:NodeId -> Temp {
        if (id == NO_NODE) { return NO_TEMP; }
        k: Lit = a.expr(id).kind;
        if (k == Lit.Ptr || k == Lit.Ref) { return self.lowerExpr(a, id); }
        return self.lowerAddress(a, id);
    }

    // The byte offset of `field` within whatever `base` is a struct of.
    // Where a field sits inside its struct. Every failure here used to answer 0, which is a
    // valid offset (the first field) so a base whose type was never resolved silently read and
    // wrote the wrong member. That is how `gStderr.data.flush()` came to write over the mutex's
    // own lock flag. There is no answer to give when the type is unknown, so it says so.
    fieldOffset &self inout a:Ast base:NodeId field:Sym -> long {
        b: Expr = a.expr(base);
        // A `str` or a slice is a fat pointer, not a struct: `.ptr` and `.len` are its two words,
        // and its companion name is the element's, which no struct registry will ever hold.
        if (b.kind == Lit.Str || b.kind == Lit.Slice) {
            if (nameOf(field) == "ptr") { return 0; }
            if (nameOf(field) == "len") { return 8; }
            failStr(format("a {} has only '.ptr' and '.len', not '.{}'",
                           typeName(b.kind), nameOf(field)));
        }
        // Each of the three below used to print and answer 0. The checker refuses all three now
        // (`Checker::checkField`), so reaching one here is this compiler's own bug rather than
        // the program's -- and 0 is the wrong answer to give either way, since it is the first
        // field's own offset and reads back as some other member's value. They stop the compile.
        owner: Sym = b.structName;     // a `*T` names T here, which is whose field this is
        if (owner == NO_SYM) {
            failStr(format("internal: '.{}' on a value with no struct type reached lowering",
                           nameOf(field)));
        }
        at: long = gReg.findStruct(nameOf(owner));
        if (at < 0) {
            failStr(format("internal: '{}.{}' — {} was never laid out (kind {})",
                           nameOf(owner), nameOf(field), nameOf(owner), typeName(b.kind)));
        }
        d: StructDef = gReg.structDef(at);
        k: long = gReg.findFieldSym(d, field);
        if (k < 0) {
            failStr(format("internal: {} has no field '{}', and it reached lowering",
                           nameOf(owner), nameOf(field)));
        }
        return gReg.fieldAt(d, k).offset;
    }

    constTemp &self v:long k:Lit -> Temp {
        t: Temp = self.ir.newTemp(k, NO_SYM);
        in: Instr = instr(IROp.Const);
        in.dst = t;
        in.imm = v;
        in.kind = k;
        self.ir.emit(in);
        return t;
    }

    // `p.x` as a value: the address, then a load of the field's width through it.
    lowerFieldRead &self inout a:Ast id:NodeId -> Temp {
        e: Expr = a.expr(id);
        // A fat pointer's own fields: the value is the address of the pair, so there is no
        // separate address to take.
        p: Payload = e.payload;
        match p {
            Field(f) {
                fn: FieldNode = a.fields.get(f);
                bk: Lit = a.expr(fn.base).kind;
                if (bk == Lit.Str || bk == Lit.Slice) {
                    base: Temp = self.lowerExpr(a, fn.base);
                    t: Temp = self.ir.newTemp(e.kind, e.structName);
                    ld: Instr = instr(IROp.PtrLoad);
                    ld.dst = t;
                    ld.a = base;
                    ld.imm = 0;
                    if (nameOf(fn.name) == "len") { ld.imm = 8; }
                    ld.kind = e.kind;
                    self.ir.emit(ld);
                    // `.ptr` hands out the raw base address, and a raw address is not a typed
                    // pointer: `s.ptr + i` counts bytes, which is what every caller of it writes:
                    //  `strCmp`'s `loadByte(s.ptr + i)`, `strSlice`'s `(s.ptr + from)`. Left
                    // tracked, the companion name a slice carries (its element's) would scale
                    // those by the element width, and on a `str`, whose companion is empty, by
                    // the eight bytes an unnamed pointee defaults to. The one way to get a typed
                    // pointer out of a fat one is the cast the callers already write.
                    self.ir.notePointee(t, NO_SYM);
                    return t;
                }
            }
            _ { }
        }
        addr: Temp = self.lowerAddress(a, id);
        if (addr == NO_TEMP) { return NO_TEMP; }
        // A field that is itself an aggregate lives inside its owner: its address is the value,
        // and loading through it would hand back the first eight bytes of one. A ref field is the
        // opposite case. It holds a pointer, so its value is a load.
        if (storedInline(e.kind, e.structName)) { return addr; }
        t: Temp = self.ir.newTemp(e.kind, e.structName);
        in: Instr = instr(IROp.PtrLoad);
        in.dst = t;
        in.a = addr;
        in.imm = 0;
        in.kind = storedKind(e.kind, e.structName);
        self.ir.emit(in);
        return t;
    }

    // `p.x = v`: the address, then the store.
    lowerFieldWrite &self inout a:Ast target:NodeId v:Temp -> void {
        addr: Temp = self.lowerAddress(a, target);
        if (addr == NO_TEMP) { return; }
        in: Instr = instr(IROp.PtrStore);
        in.a = addr;
        in.b = v;
        in.imm = 0;
        in.kind = storedKind(a.expr(target).kind, a.expr(target).structName);
        self.ir.emit(in);
    }
}

methods Lowerer {
    // ─── arrays ──────────────────────────────────────────────────────────────
    //
    // An element's address is the array's base plus the index scaled by the element's width. The
    // scale is what makes indexing type-aware: get it wrong and every access is off by a factor,
    // silently.

    // Does `base` name storage declared as a fixed array: a local, a parameter, or a struct
    // field? The expression node cannot say: an array's kind is its element's, so a `[str; N]`
    // reads as a `str` and a `[[T]; N]` as a slice. Both callers ask a table that only something
    // declared with a count answers, so a real `str` or slice says no. Emits nothing, which is
    // what lets it be asked as a predicate on a path that has not committed to lowering yet.
    isFixedArray &self inout a:Ast base:NodeId -> bool {
        p: Payload = a.expr(base).payload;
        match p {
            Name(n)  { return self.arrayCount(n) != NOT_FOUND; }
            Field(_) { return self.fieldArrayDef(a, base).name != NO_SYM; }
            _ { }
        }
        return false;
    }

    // The address of `xs[i]`.
    // The bytes an index runs over. A fixed array is its storage, so its address is the base; a
    // `str` or a slice is a fat pointer to storage somewhere else, so the base is the word that
    // pointer holds -- indexing off the pair itself reads the pair.
    // `raw` is the checker's own answer to "is this base a raw pointer", written onto the index
    // node however the pointer was spelled. Asked instead of re-deriving it from the base's type,
    // because a base that is an expression need not carry one this pass can recognise: `(q + 1)`
    // arrives typed by its literal operand, and reading the type sent it down the take-the-
    // address path, where a binary operator is no place at all and the whole slice lowered to
    // nothing, a `convert` with no operand, and a segfault reading the header it never built.
    indexBase &self inout a:Ast base:NodeId raw:bool -> Temp {
        bk: Lit = a.expr(base).kind;
        if (bk == Lit.Ptr || raw) { return self.lowerExpr(a, base); }
        // A fixed array is its storage even when its element is a fat pointer, and the node
        // carries the element's kind, so `[str; N]` and `[[T]; N]` are indistinguishable from one
        // `str` or one slice here. Asked before the pair branch, which would otherwise read
        // element zero's pointer as the address of the whole run.
        if (!self.isFixedArray(a, base) && (bk == Lit.Str || bk == Lit.Slice)) {
            pair: Temp = self.lowerExpr(a, base);
            if (pair == NO_TEMP) { return NO_TEMP; }
            return self.loadWord(pair, 0);
        }
        at: Temp = self.placeOf(a, base);
        if (at != NO_TEMP) { return at; }
        // Nothing with an address, and no fat pointer either: the base is an expression. Lower it
        // as a value: `(q + 1)[..3]` is a run of bytes reached through the pointer that
        // expression yields, and taking its address instead answered nothing at all, so the whole
        // slice lowered to a `convert` with no operand. `placeOf` declines without emitting for
        // exactly the shapes that reach here, so this lowers the base once.
        return self.lowerExpr(a, base);
    }


    // How many elements the thing being indexed holds, as a temp: a fat pointer carries it, a
    // fixed array had it written down. NO_TEMP when neither, which only a raw pointer is.
    lengthOf &self inout a:Ast base:NodeId -> Temp {
        e: Expr = a.expr(base);
        // A written-down count is asked for first. An array carries its element's kind on the
        // node, so `[str; 47]` and `[[T]; N]` look exactly like one `str` or one slice here, and
        // reading the first sixteen bytes of the array as a {ptr, len} pair answers with element
        // zero's length, which for a zero-filled table is 0 and puts every index out of range.
        // `arrayCount` and `fieldArrayDef` both answer only for something declared as an array,
        // so a real `str` or slice falls through to the pair below exactly as it did.
        pl: Payload = e.payload;
        match pl {
            Name(n) {
                c: long = self.arrayCount(n);
                if (c != NOT_FOUND) { return self.constTemp(c, Lit.Long); }
            }
            Field(_) {
                fd: FieldDef = self.fieldArrayDef(a, base);
                if (fd.name != NO_SYM) { return self.constTemp(fd.count, Lit.Long); }
            }
            _ { }
        }
        if (e.kind == Lit.Str || e.kind == Lit.Slice) {
            pair: Temp = self.lowerExpr(a, base);
            if (pair == NO_TEMP) { return NO_TEMP; }
            return self.loadWord(pair, 8);
        }
        return NO_TEMP;
    }

    // Trap unless (unsigned) `idx` < `len`. Unsigned, so a negative index is an enormous one and
    // fails the same compare. One test rather than two. A range bound is inclusive (`hi <= len`,
    // `lo <= hi`) and says so, because it is a different mistake with a different wording.
    // `at` is where the `[` was written: the one thing a failed check cannot work out for
    // itself, and the only part of the message that says which index of the program went wrong.
    // A synthesized index (one no source line produced) carries NO_SYM, and the report leaves the
    // location off rather than naming somewhere arbitrary.
    boundsCheck &self idx:Temp len:Temp range:bool at:Sym -> void {
        if (idx == NO_TEMP || len == NO_TEMP) { return; }
        in: Instr = instr(IROp.Bounds);
        in.a = idx;
        in.b = len;
        in.name = at;
        if (range) { in.imm = 1; }
        self.ir.emit(in);
    }

    // The length of what an index is over, but only where asking cannot run anything twice.
    // `lengthOf` lowers its base again, so a base that is a call would be called once for the
    // element and once for the check, and a name or a field costs nothing to reach twice.
    checkableLength &self inout a:Ast base:NodeId -> Temp {
        if (base == NO_NODE) { return NO_TEMP; }
        p: Payload = a.expr(base).payload;
        match p {
            Name(_)  { return self.lengthOf(a, base); }
            Field(_) { return self.lengthOf(a, base); }
            _ { }
        }
        return NO_TEMP;
    }

    // `a[..]`, `a[i..j]`, `a[..j]`, `a[i..]`: a fresh {ptr, len} pair over part of something
    // that already has one, or over a fixed array, which is what decays it to a slice.
    lowerSliceOf &self inout a:Ast ix:IndexNode elemSize:long -> Temp {
        data: Temp = NO_TEMP;
        total: Temp = NO_TEMP;
        fat: bool = self.isFatBase(a, ix.base, ix.rawPointerBase);
        if (fat) {
            pair: Temp = self.lowerExpr(a, ix.base);
            if (pair == NO_TEMP) { return NO_TEMP; }
            data = self.loadWord(pair, 0);
            total = self.loadWord(pair, 8);
        } else {
            data = self.indexBase(a, ix.base, ix.rawPointerBase);
        }
        if (data == NO_TEMP) { return NO_TEMP; }
        // A raw pointer carries no length (that is what makes walking one `unsafe`) and its
        // stride is the pointee the temp records, not the type the base expression happens to
        // have been given: `(q + 1)` on a `*u8` is typed by its literal operand.
        step: long = elemSize;
        if (ix.rawPointerBase) {
            pn: Sym = self.ir.pointeeOf(data);
            if (pn != NO_SYM) { step = namedWidth(pn); }
        } else if (!fat) {
            total = self.lengthOf(a, ix.base);
        }

        from: Temp = NO_TEMP;
        if (ix.sliceStart != NO_NODE) { from = self.lowerExpr(a, ix.sliceStart); }
        upto: Temp = total;
        if (ix.sliceEnd != NO_NODE) { upto = self.lowerExpr(a, ix.sliceEnd); }

        // The two ways a range can be wrong, each inclusive: the far bound past the end, and the
        // bounds the wrong way round. `hi <= len` first, so `xs[5..2]` on a length of 3 reports
        // the bound it exceeded rather than the order it was written in.
        if (ix.sliceEnd != NO_NODE) { self.boundsCheck(upto, total, true, ix.at); }
        if (from != NO_TEMP && upto != NO_TEMP) { self.boundsCheck(from, upto, true, ix.at); }

        start: Temp = data;
        len: Temp = upto;
        if (from != NO_TEMP) {
            start = self.addScaled(data, from, step);
            if (upto != NO_TEMP) { len = self.arith(IROp.Sub, upto, from, Lit.Long); }
        }
        if (len == NO_TEMP) { len = self.constTemp(0, Lit.Long); }

        hdr: Temp = self.aggSlotFor(16);
        self.storeAt(hdr, 0, start, Lit.Ptr);
        self.storeAt(hdr, 8, len, Lit.Long);
        return hdr;
    }

    arith &self op:IROp x:Temp y:Temp k:Lit -> Temp {
        t: Temp = self.ir.newTemp(k, NO_SYM);
        in: Instr = instr(op);
        in.dst = t; in.a = x; in.b = y; in.kind = k;
        self.ir.emit(in);
        return t;
    }

    // `base + i * width`, with the multiply left out when the width is one.
    addScaled &self base:Temp idx:Temp width:long -> Temp {
        step: Temp = idx;
        if (width != 1) { step = self.arith(IROp.Mul, idx, self.constTemp(width, Lit.Long), Lit.Long); }
        return self.arith(IROp.Add, base, step, Lit.Ptr);
    }

    // A `str` or a slice reached as a value (not a fixed array, not a raw pointer): its pair is
    // lowered once and both words read from it, so `f()[i]` or `xs[1..3][0]` is checked against
    // the length that pair carries without running the base twice.
    isFatBase &self inout a:Ast base:NodeId raw:bool -> bool {
        if (base == NO_NODE || raw) { return false; }
        bk: Lit = a.expr(base).kind;
        return (bk == Lit.Str || bk == Lit.Slice) && !self.isFixedArray(a, base);
    }

    lowerElemAddress &self inout a:Ast ix:IndexNode elemSize:long -> Temp {
        base: Temp = NO_TEMP;
        len: Temp = NO_TEMP;
        fat: bool = self.isFatBase(a, ix.base, ix.rawPointerBase);
        if (fat) {
            pair: Temp = self.lowerExpr(a, ix.base);
            if (pair == NO_TEMP) { return NO_TEMP; }
            base = self.loadWord(pair, 0);
            len = self.loadWord(pair, 8);
        } else {
            base = self.indexBase(a, ix.base, ix.rawPointerBase);
        }
        if (base == NO_TEMP) { return NO_TEMP; }
        if (ix.index == NO_NODE) { return base; }
        idx: Temp = self.lowerExpr(a, ix.index);
        // Checked before the address is formed, and only where a length is known: a raw `*T` has
        // none, which is exactly why walking one is `unsafe`.
        if (!fat) { len = self.checkableLength(a, ix.base); }
        self.boundsCheck(idx, len, false, ix.at);
        // Over a raw pointer the stride is the pointee the base temp records, not the type the
        // base expression carries: an index whose base is itself an index or a piece of pointer
        // arithmetic need not be typed as one.
        width: long = elemSize;
        pn: Sym = self.ir.pointeeOf(base);
        if (pn != NO_SYM && ix.rawPointerBase) { width = namedWidth(pn); }
        scaled: Temp = idx;
        if (width != 1) {
            k: Temp = self.constTemp(width, Lit.Long);
            scaled = self.ir.newTemp(Lit.Long, NO_SYM);
            m: Instr = instr(IROp.Mul);
            m.dst = scaled;
            m.a = idx;
            m.b = k;
            m.kind = Lit.Long;
            self.ir.emit(m);
        }
        t: Temp = self.ir.newTemp(Lit.Ptr, NO_SYM);
        in: Instr = instr(IROp.Add);
        in.dst = t;
        in.a = base;
        in.b = scaled;
        in.kind = Lit.Long;
        self.ir.emit(in);
        // An element of a run of T is a T: the address of one points at the same thing the base
        // did, and losing that is what makes `p[i][j]` walk the inner row by bytes.
        self.ir.notePointee(t, pn);
        return t;
    }

    // `Name { f: v, ... }`: built directly into a scratch slot, field by field, and the slot's
    // address is the literal's value. Nothing is materialised twice: an initializer that is itself
    // an aggregate is copied straight into its field's place.
    lowerStructLit &self inout a:Ast id:NodeId l:long -> Temp {
        e: Expr = a.expr(id);
        ln: LitNode = a.lits.get(l);
        bytes: long = structBytes(e.structName);
        slot: long = self.ir.addAggSlot(bytes);
        base: Temp = self.ir.newTemp(Lit.Ptr, e.structName);
        sl: Instr = instr(IROp.AggSlot);
        sl.dst = base;
        sl.imm = slot;
        sl.kind = Lit.Ptr;
        self.ir.emit(sl);

        at: long = gReg.findStruct(nameOf(e.structName));
        if (at < 0) { return base; }
        d: StructDef = gReg.structDef(at);
        k: long = 0;
        // `..rest` lands whole first and the named fields overwrite it. One copy rather than a
        // store per unnamed field, and the type is Copy so the copy is all the value is.
        if (ln.rest != NO_NODE) {
            src: Temp = self.placeOf(a, ln.rest);
            self.copyInto(base, src, bytes);
        }
        // A literal naming fewer fields than the struct has leaves the rest, so `T { tag: 1 }`
        // over a `[str; 4]` is the ordinary case.
        // The slot is scratch frame storage holding whatever the last call left in it, so the
        // whole of it is zeroed before the named fields are written over the top.
        else if (ln.initCount < d.fieldCount) { self.zeroFill(base, bytes); }
        for k in 0..ln.initCount {
            ini: InitNode = a.inits.get(ln.firstInit + k);
            fi: long = gReg.findFieldSym(d, ini.name);
            if (fi >= 0) {
                f: FieldDef = gReg.fieldAt(d, fi);
                where: Temp = base;
                if (f.offset != 0) {
                    off: Temp = self.constTemp(f.offset, Lit.Long);
                    where = self.ir.newTemp(Lit.Ptr, f.structName);
                    add: Instr = instr(IROp.Add);
                    add.dst = where;
                    add.a = base;
                    add.b = off;
                    add.kind = Lit.Long;
                    self.ir.emit(add);
                }
                // `xs: [a, b, c]`: every element, in place (the checker held it to the length).
                if (f.isArray && a.expr(ini.value).op == Op.ArrayLit) {
                    self.lowerArrayInto(a, where, ini.value);
                } else if (storedInline(f.kind, f.structName)) {
                    src: Temp = self.placeOf(a, ini.value);
                    self.copyInto(where, src, aggregateBytes(f.kind, f.structName));
                } else {
                    v: Temp = self.lowerExpr(a, ini.value);
                    st: Instr = instr(IROp.PtrStore);
                    st.a = where;
                    st.b = v;
                    st.kind = storedKind(f.kind, f.structName);
                    self.ir.emit(st);
                }
            }
        }
        return base;
    }

    // Zero `size` bytes at `base[0..size)`, in word-sized chunks: the widest that still fits,
    // so a struct (whose size is always rounded to eight) costs one store per eight bytes. Past
    // `UNROLL_COPY_BYTES` one block zero instead (`rep stosq`): a `BufWriter` literal's 4 KiB buffer was
    // 512 stores, in every program that prints.
    zeroFill &self base:Temp size:long -> void {
        if (base == NO_TEMP) { return; }
        if (size > UNROLL_COPY_BYTES) {
            zi: Instr = instr(IROp.AggZero);
            zi.a = base;
            zi.imm = size;
            self.ir.emit(zi);
            return;
        }
        z: Temp = self.constTemp(0, Lit.Long);
        o: long = 0;
        while (o < size) {
            c: long = 1;
            wt: Lit = Lit.Char;
            if (size - o >= 8)      { c = 8; wt = Lit.Long; }
            else if (size - o >= 4) { c = 4; wt = Lit.Int; }
            st: Instr = instr(IROp.PtrStore);
            st.a = base;
            st.b = z;
            st.imm = o;
            st.kind = wt;
            self.ir.emit(st);
            o = o + c;
        }
    }

    copyInto &self dst:Temp src:Temp bytes:long -> void {
        if (dst == NO_TEMP || src == NO_TEMP) { return; }
        cp: Instr = instr(IROp.AggCopy);
        cp.a = dst;
        cp.b = src;
        cp.imm = bytes;
        self.ir.emit(cp);
    }

    // The declaration of the array field an index is over, or a row named NO_SYM when the base is
    // not one. An inline array field is the one place the index expression's own type does not
    // answer: `self.data[i]` on a `[int; 4]` arrives typed `long`, and reading eight bytes of a
    // four-byte element returns two of them at once: `at0` came back as 10 << 32.
    fieldArrayDef &self inout a:Ast base:NodeId -> FieldDef {
        none: FieldDef = FieldDef { name: NO_SYM, kind: Lit.Void, structName: NO_SYM,
                                    offset: 0, isArray: false, count: 0 };
        if (base == NO_NODE) { return none; }
        fi: long = -1;
        p: Payload = a.expr(base).payload;
        match p { Field(f) { fi = f; } _ { } }
        if (fi < 0) { return none; }
        fn: FieldNode = a.fields.get(fi);
        owner: Sym = self.ownerStructOf(a, fn.base);
        if (owner == NO_SYM) { return none; }
        at: long = gReg.findStruct(nameOf(owner));
        if (at < 0) { return none; }
        d: StructDef = gReg.structDef(at);
        k: long = gReg.findFieldSym(d, fn.name);
        if (k < 0) { return none; }
        f: FieldDef = gReg.fieldAt(d, k);
        // A count of zero means the declaration recorded none, not an array of no elements: the
        // length is unknown, and answering 0 would make every index of it out of range.
        if (!f.isArray || f.count <= 0) { return none; }
        return f;
    }

    // The struct an expression is of. Usually the node says so; an index over an array field may
    // not, and then the field's element type does: `g.rows[0]` is a `Row` because `rows` was
    // declared `[Row; 2]`. Without this the chain `g.rows[0].cells` found no field, so
    // `cells[..]` built a header of length zero.
    ownerStructOf &self inout a:Ast id:NodeId -> Sym {
        if (id == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(id);
        if (e.structName != NO_SYM) { return e.structName; }
        p: Payload = e.payload;
        match p {
            Index(i) {
                fd: FieldDef = self.fieldArrayDef(a, a.indexes.get(i).base);
                if (fd.name != NO_SYM) { return fd.structName; }
            }
            _ { }
        }
        return NO_SYM;
    }

    // How wide one element of the thing being indexed is.
    elemWidth &self inout a:Ast id:NodeId -> long {
        e: Expr = a.expr(id);
        if (e.kind == Lit.Struct && e.structName != NO_SYM) {
            at: long = gReg.findStruct(nameOf(e.structName));
            if (at >= 0) { return gReg.structDef(at).size; }
        }
        n: long = typeInfo(e.kind).size;
        if (n < 1) { n = 8; }
        return n;
    }

    // One element of whatever `base` is a sequence of. A slice expression's own type is `slice`,
    // so its width has to come from the base rather than from the node being built.
    // A fixed array is asked first: its node carries the element's kind, so a `[str; 3]` looks
    // like one `str`, and `ss[1..]` stepped one byte into the array instead of one element.
    baseElemWidth &self inout a:Ast base:NodeId -> long {
        e: Expr = a.expr(base);
        fd: FieldDef = self.fieldArrayDef(a, base);
        if (fd.name != NO_SYM) { return typeBytes(fd.kind, fd.structName); }
        if (self.isFixedArray(a, base)) { return self.elemWidth(a, base); }
        if (e.kind == Lit.Str) { return 1; }
        if (e.kind == Lit.Slice) { return namedWidth(e.structName); }
        return self.elemWidth(a, base);
    }

    lowerIndexRead &self inout a:Ast id:NodeId -> Temp {
        e: Expr = a.expr(id);
        p: Payload = e.payload;
        at: long = -1;
        match p { Index(i) { at = i; } _ { } }
        if (at < 0) { return NO_TEMP; }
        ix: IndexNode = a.indexes.get(at);
        // `a[..]` and `a[i..j]` do not read an element: they make a new fat pointer over some of
        // the old one, which is also how a fixed array becomes a slice.
        if (ix.whole || ix.sliceStart != NO_NODE || ix.sliceEnd != NO_NODE) {
            return self.lowerSliceOf(a, ix, self.baseElemWidth(a, ix.base));
        }
        ek: Lit = e.kind;
        es: Sym = e.structName;
        fd: FieldDef = self.fieldArrayDef(a, ix.base);
        if (fd.name != NO_SYM) { ek = fd.kind; es = fd.structName; }
        addr: Temp = self.lowerElemAddress(a, ix, typeBytes(ek, es));
        if (addr == NO_TEMP) { return NO_TEMP; }
        // An element that is itself an aggregate lives in the array: its address is its value.
        if (storedInline(ek, es)) { return addr; }
        t: Temp = self.ir.newTemp(ek, es);
        in: Instr = instr(IROp.PtrLoad);
        in.dst = t;
        in.a = addr;
        in.kind = storedKind(ek, es);
        self.ir.emit(in);
        return t;
    }

    lowerIndexWrite &self inout a:Ast target:NodeId v:Temp -> void {
        e: Expr = a.expr(target);
        p: Payload = e.payload;
        at: long = -1;
        match p { Index(i) { at = i; } _ { } }
        if (at < 0) { return; }
        ix: IndexNode = a.indexes.get(at);
        ek: Lit = e.kind;
        es: Sym = e.structName;
        fd: FieldDef = self.fieldArrayDef(a, ix.base);
        if (fd.name != NO_SYM) { ek = fd.kind; es = fd.structName; }
        addr: Temp = self.lowerElemAddress(a, ix, typeBytes(ek, es));
        if (addr == NO_TEMP) { return; }
        in: Instr = instr(IROp.PtrStore);
        in.a = addr;
        in.b = v;
        in.kind = storedKind(ek, es);
        self.ir.emit(in);
    }
}

methods Lowerer {
    // ─── inline assembly ─────────────────────────────────────────────────────
    //
    // The pieces keep their source order, because the literal lines are emitted verbatim between
    // the register moves. Inputs are evaluated before the block, outputs stored after it, which
    // is what lets an `asm` block read and write ordinary variables.
    lowerAsm &self inout a:Ast at:long -> void {
        n: AsmNode = a.asms.get(at);
        first: long = self.ir.asmKinds.len();
        for k in 0..n.pieceCount {
            piece: AsmPiece = a.asmPieces.get(n.firstPiece + k);
            v: Temp = NO_TEMP;
            size: long = 8;
            if (piece.kind == AsmKind.In) {
                v = self.lowerExpr(a, piece.value);
                size = typeInfo(self.ir.kindOf(v)).size;
            }
            self.ir.addAsmPiece(piece.kind, piece.reg, piece.name, v, piece.text, size);
        }
        in: Instr = instr(IROp.Asm);
        in.firstPiece = first;
        in.pieceCount = n.pieceCount;
        self.ir.emit(in);
    }
}

// The `@init` and `@fini` functions, in the order the program's modules were read (dependencies
// first): `_start` calls the first before any startup initializer, and `__kiln_fini` (which the
// entry object defines, and `_start` and the `exit` builtin call) the second in reverse. And
// whether this object calls `__kiln_fini` from outside.
pub var gInitHooks: Vec<Sym> = vec![];
pub var gFiniHooks: Vec<Sym> = vec![];
pub var gUsesFini: bool = false;

// The startup initializer's name: `$globalInit` for a whole program, and `$init$<package>` in a
// package build, where every package has its own and the program's `_start` runs them all.
pub initFunctionName -> Sym {
    if (!gKlibMode || gThisPkg == NO_SYM) { return intern("$globalInit"); }
    // A package with no manifest is named by its file's path, which is not an identifier.
    s: String;
    s.pushStr("$init$");
    p: str = nameOf(gThisPkg);
    for i in 0..p.len {
        c: long = charAt(p, i);
        if (isIdentPart(c)) { s.push(c as char); } else { s.push('_'); }
    }
    return internString(s);
}
