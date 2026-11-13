// Inlining across packages: the IR of a package's small exported functions, carried in its
// `.klib` (the IR chunk), and read back by a dependent so that its inliner can copy them.
//
// The owner keeps, after its first optimizer pass, every function it exports -- its own source
// functions, and the generic instance functions it compiled -- that the inliner would copy
// (`inlinableIR`: small, no frame slot, no array slot, no `asm`) and that holds nothing another
// object cannot have: no vtable address (a vtable is local to each object). What it calls or takes
// the address of is written as the link label the owner's own code uses, and only when another
// object can link to that label too; a body with one it cannot is not shipped. Temps are numbered
// from 0 with their types, a string literal travels as its text, a scratch slot as its size.
//
// A dependent, after lowering and its own first optimizer pass, reads in the body of each external
// function its code calls that has one (`importInlinable`) as a function that is never emitted
// (`IRFunc.imported`; the inliner drops it once it has copied it), and the inliner, the second
// optimizer pass and `flow.k` see through the call exactly as in a whole-program build. A call
// inside such a body names its callee as `=<label>` (`fnLabel` writes the label as it is).
#include <{ir, asm, relayout}>
#include <parse::{registry, types, upstream}>
#include <support::compiler>
#include <stdlib::{encode, map, option, string, vec}>

// ─── writing ─────────────────────────────────────────────────────────────────

// One body kept for the `.klib`: whose it is, the functions it names (a run in `gShipCallees`,
// resolved to labels once the object is written and its exports are known), and its bytes.
pub struct ShipBody { name: Sym, firstCallee: long, calleeCount: long, at: long, len: long }
pub var gShipBodies: Vec<ShipBody> = vec![];
pub var gShipCallees: Vec<Sym> = vec![];
pub var gShipOut: Encoder;
// The bodyless functions a shipped body calls: another object's, linked by the label their name
// spells.
pub var gShipDeclared: HashMap<str, bool> = map![];

// After the first optimizer pass: every exported function the inliner could copy, encoded.
pub snapshotInlinable inout p:IRProgram -> void {
    for f in 0..p.funcs.len() {
        fn: IRFunc = p.funcs.get(f);
        if (fn.isMain || fn.imported) { continue; }
        if (!fn.isPub && !gInstanceFp.has(nameOf(fn.name))) { continue; }
        if (!inlinableIR(p, fn)) { continue; }
        shipOne(p, fn);
    }
}

local shipOne inout p:IRProgram fn:IRFunc -> void {
    callees: HashMap<long, long>;
    firstCallee: long = gShipCallees.len();
    out: Encoder;
    n: long = fn.tempCount - fn.firstTemp;
    out.putLen(n);
    for t in fn.firstTemp..fn.tempCount {
        out.putVarint(p.tempKinds.get(t) as long);
        p.tempStructs.get(t).encode(out);
        p.tempPointees.get(t).encode(out);
    }
    real: long = 0;
    for k in 0..fn.instrCount {
        if (p.code.get(fn.firstInstr + k).op != IROp.Nop) { real = real + 1; }
    }
    out.putLen(real);
    for k in 0..fn.instrCount {
        in: Instr = p.code.get(fn.firstInstr + k);
        if (in.op == IROp.Nop) { continue; }
        if (in.op == IROp.VtableAddr || in.op == IROp.Asm) { gShipCallees.truncate(firstCallee); return; }
        out.putVarint(in.op as long);
        if (!shipTemp(&out, fn, in.dst) || !shipTemp(&out, fn, in.a)) { gShipCallees.truncate(firstCallee); return; }
        flags: long = 0;
        if (in.bIsImm) { flags = flags | 1; }
        if (in.paramSeed) { flags = flags | 2; }
        if (in.promoted) { flags = flags | 4; }
        if (in.noReturn) { flags = flags | 8; }
        if (in.isGlobal) { flags = flags | 16; }
        out.putLen(flags);
        if (in.bIsImm) { out.putVarint(in.bImm); }
        else if (!shipTemp(&out, fn, in.b)) { gShipCallees.truncate(firstCallee); return; }
        // An index into this program's tables travels as what it indexes.
        if (in.op == IROp.StrAddr || in.op == IROp.StrLitVal) { p.strings.get(in.imm).encode(out); }
        else if (in.op == IROp.AggSlot) { out.putVarint(p.aggSlots.get(in.imm)); }
        else { out.putVarint(in.imm); }
        out.putVarint(in.cmpOp as long);
        if (in.op == IROp.Call || in.op == IROp.FnAddr) {
            hit: Option<long> = callees.find(in.name as long);
            c: long = -1;
            match hit { Some(i) { c = i; } None {
                c = gShipCallees.len() - firstCallee;
                callees.put(in.name as long, c);
                gShipCallees.push(in.name);
                if (isDeclaredExtern(p, in.name)) { gShipDeclared.put(nameOf(in.name), true); }
            } }
            out.putLen(c);
        } else {
            in.name.encode(out);
        }
        in.structName.encode(out);
        out.putVarint(in.kind as long);
        out.putVarint(in.fromKind as long);
        out.putVarint(in.toKind as long);
        out.putLen(in.argCount);
        for j in 0..in.argCount {
            if (!shipTemp(&out, fn, p.args.get(in.firstArg + j))) { gShipCallees.truncate(firstCallee); return; }
        }
    }
    at: long = gShipOut.len();
    unsafe { gShipOut.putRaw(out.view()); }
    gShipBodies.push(ShipBody { name: fn.name, firstCallee: firstCallee, calleeCount: gShipCallees.len() - firstCallee,
                                at: at, len: gShipOut.len() - at });
}

// A temp of `fn` as its place in the function's own run (NO_TEMP as -1). One outside the run is
// another function's, and a body holding one is not shipped.
local shipTemp inout out:Encoder fn:IRFunc t:Temp -> bool {
    if (t == NO_TEMP) { out.putVarint(-1); return true; }
    if (t < fn.firstTemp || t >= fn.tempCount) { return false; }
    out.putVarint(t - fn.firstTemp);
    return true;
}

// The IR chunk, once the object is written: each kept body whose function was exported, under
// the label a dependent calls it by, with every function it names as a label another object can
// link. A body naming one that cannot be linked (a local symbol of this object) is left out.
pub writeShipChunk inout out:Encoder -> void {
    exported: HashMap<str, bool>;
    for s in gExportedSyms { exported.put(s, true); }
    inst: HashMap<str, bool>;
    for k in 0..gExportedInst.len() { inst.put(nameOf(gExportedInst.get(k)), true); }
    kept: Vec<long>;
    labels: Vec<Sym>;
    firstLabel: Vec<long>;
    for b in 0..gShipBodies.len() {
        sb: ShipBody = gShipBodies.get(b);
        own: str = "";
        if (inst.has(nameOf(sb.name))) { own = instanceAlias(nameOf(sb.name)); }
        else if (exported.has(fnLabel(nameOf(sb.name)))) { own = fnLabel(nameOf(sb.name)); }
        else { continue; }
        first: long = labels.len();
        labels.push(intern(own));
        ok: bool = true;
        for c in 0..sb.calleeCount {
            n: str = nameOf(gShipCallees.get(sb.firstCallee + c));
            l: str = "";
            if (gLinkAlias.has(n)) { l = fnLabel(n); }                        // a dependency's instance
            else if (inst.has(n)) { l = instanceAlias(n); }                   // one compiled here
            else if (exported.has(fnLabel(n)) || gUseSyms.has(fnLabel(n)) || gShipDeclared.has(n)) { l = fnLabel(n); }
            else { ok = false; break; }
            labels.push(intern(l));
        }
        if (!ok) { labels.truncate(first); continue; }
        kept.push(b);
        firstLabel.push(first);
    }
    out.putLen(kept.len());
    for k in 0..kept.len() {
        sb: ShipBody = gShipBodies.get(kept.get(k));
        first: long = firstLabel.get(k);
        labels.get(first).encode(out);
        rec: Encoder;
        rec.putLen(sb.calleeCount);
        for c in 0..sb.calleeCount { labels.get(first + 1 + c).encode(rec); }
        unsafe {
            all: [u8] = gShipOut.view();
            rec.putRaw(all[sb.at..sb.at + sb.len]);
            out.putBytes(rec.view());
        }
    }
}

// ─── reading ─────────────────────────────────────────────────────────────────

// A body a loaded `.klib` carries, by its label: where its record is, and the string table it
// reads names through.
pub struct ShipRef { at: long, len: long, symBase: long, symCount: long }
pub var gShipRefs: Vec<ShipRef> = vec![];
pub var gShipAt: HashMap<str, long> = map![];

// The IR chunk of a `.klib` whose names are read through the table at `symBase`. The first body
// under a label wins: packages are loaded below-first, and a label belongs to one package.
pub readShipChunk inout c:Decoder symBase:long symCount:long -> void {
    k: long = c.getLen();
    while (k > 0 && c.ok()) {
        label: Sym = Sym.decode(c);
        rec: [u8] = c.getBytes();
        at: long = 0;
        unsafe { at = rec.ptr as long; }
        if (!gShipAt.has(nameOf(label))) {
            gShipAt.put(nameOf(label), gShipRefs.len());
            gShipRefs.push(ShipRef { at: at, len: rec.len, symBase: symBase, symCount: symCount });
        }
        k = k - 1;
    }
}

// How many bodies were read in, and how many functions they stand for, for `--time-phases`.
pub var gShipImported: long = 0;

// After the first optimizer pass: the shipped body of every external function a call here names,
// read in as a function the inliner may copy and the emitter never writes.
pub importInlinable inout p:IRProgram -> void {
    if (gShipRefs.isEmpty()) { return; }
    done: HashMap<long, bool>;
    n0: long = p.funcs.len();
    for f in 0..n0 {
        fn: IRFunc = p.funcs.get(f);
        for k in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op != IROp.Call || in.name == NO_SYM || done.has(in.name as long)) { continue; }
            done.put(in.name as long, true);
            l: str = fnLabel(nameOf(in.name));
            if (!gUseSyms.has(l)) { continue; }                 // not another object's
            r: long = gShipAt.getOr(l, -1);
            if (r >= 0) { importOne(p, in.name, gShipRefs.get(r)); }
        }
    }
}

local importOne inout p:IRProgram name:Sym r:ShipRef -> void {
    gSymInBase = r.symBase;
    gSymInCount = r.symCount;
    d: Decoder = decoderOf("" as [u8]);
    unsafe { d = decoderOf((r.at as *u8)[0..r.len]); }
    nc: long = d.getLen();
    callees: Vec<Sym>;
    for c in 0..nc {
        l: Sym = Sym.decode(d);
        callees.push(internString(format("={}", nameOf(l))));
    }
    // The temps, held to names this compile can resolve: a type it has not got means a body it
    // cannot compile, and that call stays a call.
    nt: long = d.getLen();
    kinds: Vec<Lit>; structs: Vec<Sym>; pointees: Vec<Sym>;
    for t in 0..nt {
        k: Lit = d.getVarint() as Lit;
        s: Sym = Sym.decode(d);
        pt: Sym = Sym.decode(d);
        if (!knownName(k, s) || !knownName(Lit.Ptr, pt)) { return; }
        kinds.push(k); structs.push(s); pointees.push(pt);
    }
    base: Temp = p.tempKinds.len();
    for t in 0..nt {
        tt: Temp = p.newTemp(kinds.get(t), structs.get(t));
        p.notePointee(tt, pointees.get(t));
    }
    firstInstr: long = p.code.len();
    ni: long = d.getLen();
    i: long = 0;
    while (i < ni && d.ok()) {
        in: Instr = instr(d.getVarint() as IROp);
        in.dst = readTemp(&d, base);
        in.a = readTemp(&d, base);
        flags: long = d.getLen();
        in.bIsImm = (flags & 1) != 0;
        in.paramSeed = (flags & 2) != 0;
        in.promoted = (flags & 4) != 0;
        in.noReturn = (flags & 8) != 0;
        in.isGlobal = (flags & 16) != 0;
        if (in.bIsImm) { in.bImm = d.getVarint(); in.b = NO_TEMP; } else { in.b = readTemp(&d, base); }
        if (in.op == IROp.StrAddr || in.op == IROp.StrLitVal) { in.imm = p.internString(Sym.decode(d)); }
        else if (in.op == IROp.AggSlot) { in.imm = p.addAggSlot(d.getVarint()); }
        else { in.imm = d.getVarint(); }
        in.cmpOp = d.getVarint() as IROp;
        if (in.op == IROp.Call || in.op == IROp.FnAddr) {
            c: long = d.getLen();
            if (c >= 0 && c < callees.len()) { in.name = callees.get(c); gUseSyms.put(strSlice(nameOf(in.name), 1, nameOf(in.name).len - 1), true); }
        } else {
            in.name = Sym.decode(d);
        }
        in.structName = Sym.decode(d);
        in.kind = d.getVarint() as Lit;
        in.fromKind = d.getVarint() as Lit;
        in.toKind = d.getVarint() as Lit;
        in.argCount = d.getLen();
        in.firstArg = p.args.len();
        for j in 0..in.argCount { p.args.push(readTemp(&d, base)); }
        // A global it reads or writes is another object's, which this program has to know of.
        if (in.isGlobal && in.name != NO_SYM && !p.isGlobalName(in.name)) { p.noteGlobal(in.name, 8); }
        p.emit(in);
        i = i + 1;
    }
    if (!d.done()) { failStr(format("internal: the inlinable body of '{}' did not read back ({})", nameOf(name), d.error())); }
    p.funcs.push(IRFunc { name: name, firstInstr: firstInstr, instrCount: p.code.len() - firstInstr,
                          firstTemp: base, tempCount: p.tempKinds.len(),
                          firstPromo: p.promoName.len(), promoCount: 0,
                          isPub: false, isMain: false, wantsArgs: false, imported: true });
    gShipImported = gShipImported + 1;
}

local readTemp inout d:Decoder base:Temp -> Temp {
    v: long = d.getVarint();
    if (v < 0) { return NO_TEMP; }
    return base + v;
}

// A type name another package's body uses, known here: a struct (instances and tuples are
// structs), a scalar, a function type's signature.
local knownName k:Lit s:Sym -> bool {
    if (s == NO_SYM) { return true; }
    n: str = nameOf(s);
    if (gReg.hasStruct(n) || namesScalar(n) || gReg.findEnum(n) >= 0) { return true; }
    if (k == Lit.Fn) { return gFnSigs.find(s) >= 0; }
    return false;
}
