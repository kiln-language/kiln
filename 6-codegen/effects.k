// What a call may write: interprocedural memory effects. They let `flow.k` keep what it knows
// about memory a call cannot reach, such as a `Vec`'s count across the `RawVec.reserve` its
// `push` calls on the growth path, which writes only the buffer and the capacity.
//
// A function's summary is worked out from its IR, the code that actually runs. It says:
//
//   wild            whether the function may write memory other than through its parameters:
//                   through a pointer it loaded or made up, a global, its own callees' wild
//                   writes, an `asm` block, a call through a pointer, or a call to a function
//                   with no summary.
//   per parameter   in the call's argument order, with the hidden `$sret` first where there is
//                   one: the bytes it may write relative to the pointer it was handed (a few
//                   ranges, or the whole object when an offset cannot be followed), and whether
//                   that pointer escapes. A pointer escapes when it is stored anywhere, returned,
//                   handed to `asm` or to a call through a pointer, or handed to a callee whose
//                   own parameter escapes. Two kinds are told apart: a pointer kept past the call
//                   (stored outside this function's frame, or handed to something that keeps it),
//                   and one handed back as the result, which the caller follows.
//
// What `flow.k` does with it: a frame slot whose address goes only to loads, stores and copies
// through it, and to call parameters that do not escape, is "lent" rather than exposed. Only
// those calls' parameters can hold its address, and only while the calls run, so no pointer the
// function loads and no other callee reaches it. A call then ends what is known of a lent slot
// only where the callee writes through the argument that carries the slot's address. It ends
// what is known of everything else (memory through pointers, exposed slots, globals) only when it
// is wild, or writes through a pointer argument that may point at one of those.
//
// Provenance. Each temp of the function holds a value derived from some of its parameters (a
// set), from its own frame (the address of one of its slots), or from elsewhere ("other": a value
// loaded from memory, a global's address, a named slot's contents). Arithmetic
// keeps its operands' provenance: an address plus an index stays in the object it points into,
// which is the rule C's aliasing rests on too. An offset is followed only through adding or
// subtracting a constant. A write through a temp derived from parameter k is a write to k's
// object, at that offset or anywhere in it. A write through "other" is wild, and a write through
// the frame is nothing a caller can see. A parameter's value stored anywhere escapes, since what
// is loaded back is "other" and no longer followed; so, in a wild function, a parameter whose
// value was stored (in the frame too) is taken as written anywhere, since the wild write may go
// through what was loaded back. A call's result may derive from each argument whose parameter
// the callee hands back (`fxRet`), and from every argument of a call with no summary that returns
// an address.
//
// Recursion: a callee met while its own summary is still being worked out answers "everything"
// (the call is wild, and each pointer handed to it escapes and is written all over). So does any
// callee with neither a body in this program nor a summary in a `.klib`. The summaries of a
// package's exported functions travel in its `.klib` (the EFFECTS chunk), by link label, for the
// packages that call them.
#include <{ir, asm}>
#include <parse::{ast, types, upstream}>
#include <support::compiler>
#include <stdlib::{encode, map, option, string, vec}>

// A parameter written at an offset this cannot follow, or past this many separate ranges, is
// written all over.
local MAX_RANGES: long = 8;
local MAX_PARAMS: long = 62;
// `--no-lent`: a call's conventions are not trusted in place of its callee's summary.
pub var gLentOff: bool = false;
// How deep the walk into callees goes before answering "everything".
local MAX_DEPTH: long = 256;

// The summaries: per summary its wildness and a run of parameters; per parameter whether it
// escapes, whether it is written all over, and a run of (offset, width) ranges.
pub var gFxWild: Vec<bool> = vec![];
pub var gFxPFirst: Vec<long> = vec![];
pub var gFxPCount: Vec<long> = vec![];
pub var gFxEsc: Vec<bool> = vec![];
pub var gFxAll: Vec<bool> = vec![];
pub var gFxRFirst: Vec<long> = vec![];
pub var gFxRCount: Vec<long> = vec![];
pub var gFxROff: Vec<long> = vec![];
pub var gFxRW: Vec<long> = vec![];
// A dependency's exported functions' summaries, by link label (read from its `.klib`).
pub var gFxLabel: HashMap<str, long> = map![];

// This program's functions: by name, and each one's summary once worked out (-1 not yet, -2
// being worked out, -3 none: "everything").
local var gFxFnAt: HashMap<long, long> = map![];
local var gFxOf: Vec<long> = vec![];
local var gFxReady: bool = false;
local var gFxDepth: long = 0;
local var gFxWalking: bool = false;     // a walk is using the arrays below: work out no other
pub var gFxCount: long = 0;          // summaries worked out, for `--trace-opt`
pub var gFxTop: long = 0;            // and functions whose answer is "everything"

// The provenance of the function being summarized, per temp (relative to its first).
local var pvMask: Vec<long> = vec![];     // the parameters it may derive from
local var pvOff: Vec<long> = vec![];      // the offset from them, when known
local var pvState: Vec<long> = vec![];    // 0 no parameter yet, 1 offset known, 2 offset unknown
local var pvOther: Vec<bool> = vec![];    // may be derived from elsewhere
local var pvDefs: Vec<long> = vec![];     // how many instructions write it
local var pvConst: Vec<long> = vec![];    // and the constant, when its one definition is one
local var pvIsConst: Vec<bool> = vec![];
// The summary being built: per parameter, as above, before it is copied into the tables.
local var bEsc: Vec<bool> = vec![];
local var bAll: Vec<bool> = vec![];
local var bRP: Vec<long> = vec![];         // the ranges written, each with its parameter
local var bROff: Vec<long> = vec![];
local var bRW: Vec<long> = vec![];
local var bWild: bool = false;
// Per parameter of the summary being built: whether an address derived from it is kept past the
// call (stored outside this function's frame, or handed to something that keeps it), and whether
// one is handed back as the result. Each is also an escape (`bEsc`).
local var bKept: Vec<bool> = vec![];
local var bRet: Vec<bool> = vec![];
// Per parameter: an address derived from it stored in this function's own frame, which dies with
// the call but may be read back and written through before then.
local var bFrame: Vec<bool> = vec![];
local var pvDefAt: Vec<long> = vec![];    // a temp's one definition, when it has one
pub var gFxKept: Vec<bool> = vec![];
pub var gFxRet: Vec<bool> = vec![];

// Before `flow.k` asks: this program's functions, by name. A name two functions share answers
// nothing.
pub fxBegin p:IRProgram -> void {
    gFxFnAt.clear();
    gFxOf.clear();
    for f in 0..p.funcs.len() {
        n: long = p.funcs.get(f).name as long;
        if (gFxFnAt.has(n)) { gFxFnAt.put(n, -1); } else { gFxFnAt.put(n, f); }
        gFxOf.push(-1);
    }
    gFxReady = true;
}

// The summary of what a direct call to `name` may write, or -1: everything.
pub fxOfCallee inout p:IRProgram name:Sym -> long {
    if (!gFxReady || name == NO_SYM) { return -1; }
    hit: Option<long> = gFxFnAt.find(name as long);
    f: long = -2;
    match hit { Some(x) { f = x; } None { } }
    if (f == -1) { return -1; }
    if (f >= 0) {
        fn: IRFunc = p.funcs.get(f);
        if (fn.instrCount > 0 && !fn.imported) { return fxOfFunction(p, f); }
    }
    // Another object's function: its package's summary, by the label a call links to.
    if (gFxLabel.isEmpty()) { return -1; }
    return gFxLabel.getOr(fnLabelOf(name), -1);
}

pub fxParams s:long -> long { return gFxPCount.get(s); }
pub fxWild s:long -> bool { return gFxWild.get(s); }
pub fxEscapes s:long k:long -> bool { return gFxEsc.get(gFxPFirst.get(s) + k); }
pub fxAllOver s:long k:long -> bool { return gFxAll.get(gFxPFirst.get(s) + k); }
pub fxRangeCount s:long k:long -> long { return gFxRCount.get(gFxPFirst.get(s) + k); }
pub fxRangeOff s:long k:long j:long -> long { return gFxROff.get(gFxRFirst.get(gFxPFirst.get(s) + k) + j); }
pub fxRangeW s:long k:long j:long -> long { return gFxRW.get(gFxRFirst.get(gFxPFirst.get(s) + k) + j); }
// Whether parameter k of summary s is written at all.
pub fxWrites s:long k:long -> bool { return fxAllOver(s, k) || fxRangeCount(s, k) > 0; }
// Whether an address derived from parameter k may be kept past the call (stored outside the callee's
// own frame, or handed to something that keeps it), and whether one may be the call's result.
pub fxKept s:long k:long -> bool { return gFxKept.get(gFxPFirst.get(s) + k); }
pub fxRet s:long k:long -> bool { return gFxRet.get(gFxPFirst.get(s) + k); }
// Whether a call with no summary may hand back an address derived from its arguments: when what
// it returns is an address. A number made of one takes `unsafe` code, which a summary follows
// where there is one.
pub resultHoldsAddress k:Lit -> bool { return k == Lit.Ptr || k == Lit.Ref || k == Lit.Str || k == Lit.Slice; }

// Function f's summary: its callees' first, then its own walk.
fxOfFunction inout p:IRProgram f:long -> long {
    s: long = gFxOf.get(f);
    if (s >= 0) { return s; }
    if (s == -2 || s == -3 || gFxWalking || gFxDepth >= MAX_DEPTH) { return -1; }
    gFxOf.set(f, -2);
    gFxDepth = gFxDepth + 1;
    fn: IRFunc = p.funcs.get(f);
    for i in fn.firstInstr..fn.firstInstr + fn.instrCount {
        if (p.code[i].op == IROp.Call) { fxOfCallee(p, p.code[i].name); }
    }
    gFxDepth = gFxDepth - 1;
    gFxWalking = true;
    s = summarize(p, fn);
    gFxWalking = false;
    if (s < 0) { gFxOf.set(f, -3); gFxTop = gFxTop + 1; return -1; }
    gFxOf.set(f, s);
    return s;
}

// The walk of one function, its callees' summaries in hand; -1 when the answer is "everything".
local summarize inout p:IRProgram fn:IRFunc -> long {
    first: long = fn.firstInstr;
    n: long = fn.instrCount;
    base: long = fn.firstTemp;
    nt: long = fn.tempCount - fn.firstTemp;
    if (nt < 0) { return -1; }
    // The parameters are the leading run of seeds, which the prologue counts on (`opt.k`). A
    // struct or tuple passed by value is copied by the prologue into a slot of the callee's own
    // (the seed carries how many bytes), so that slot, named by the parameter, is the frame's.
    names: Vec<Sym>;
    byVal: Vec<bool>;
    for i in first..first + n {
        in: Instr = p.code.get(i);
        if (in.op != IROp.Load || !in.paramSeed) { break; }
        names.push(in.name);
        byVal.push(in.imm > 0 && byValueAggregate(in.kind));
    }
    np: long = names.len();
    if (np > MAX_PARAMS) { return -1; }
    hasSret: bool = np > 0 && names.get(0) == intern("$sret");
    // A parameter's slot reached other than by its seed or a read means its value is no longer
    // only in the temps that read it. That is rare (a parameter whose address is taken), so the
    // answer is simply "everything".
    for i in first + np..first + n {
        o: IROp = p.code[i].op;
        if (o != IROp.Store && o != IROp.AddrOf && o != IROp.ArrStore && o != IROp.ArrLoad && o != IROp.Load && o != IROp.Asm) { continue; }
        in: Instr = p.code.get(i);
        k: long = -1;
        if (!in.isGlobal) { k = indexIn(names, in.name); }
        if (k >= 0 && !byVal.get(k) && (o == IROp.Store || o == IROp.AddrOf || o == IROp.ArrStore || o == IROp.ArrLoad
                                        || (o == IROp.Load && in.paramSeed))) { return -1; }
        if (o == IROp.Asm) {
            for k in 0..in.pieceCount { if (namedIn(names, p.asmNames.get(in.firstPiece + k))) { return -1; } }
        }
    }
    fillL(&pvMask, nt, 0);
    fillL(&pvOff, nt, 0);
    fillL(&pvState, nt, 0);
    fillB(&pvOther, nt, false);
    fillL(&pvDefs, nt, 0);
    fillL(&pvConst, nt, 0);
    fillB(&pvIsConst, nt, false);
    fillL(&pvDefAt, nt, -1);
    for i in first..first + n {
        d: Temp = p.code[i].dst;
        r: long = d - base;
        if (d == NO_TEMP || r < 0 || r >= nt || p.code[i].op == IROp.Nop) { continue; }
        pvDefs.set(r, pvDefs.get(r) + 1);
        pvDefAt.set(r, i);
        pvIsConst.set(r, p.code[i].op == IROp.Const);
        pvConst.set(r, p.code[i].imm);
    }
    // The provenance of every temp, to a fixpoint (it only grows).
    rounds: long = 0;
    going: bool = true;
    while (going) {
        if (rounds >= 12) { return -1; }
        rounds = rounds + 1;
        going = false;
        for i in first..first + n {
            d: Temp = p.code[i].dst;
            r: long = d - base;
            if (d == NO_TEMP || r < 0 || r >= nt || p.code[i].op == IROp.Nop) { continue; }
            if (defineFrom(p, i, base, nt, names, byVal, r)) { going = true; }
        }
    }
    // The writes and the escapes. A `RecoverPush` writes only its own record in this frame, and a
    // `FaultEdge` nothing, so neither is asked about; the call that links a record is a call.
    bWild = false;
    bEsc.clear(); bAll.clear(); bRP.clear(); bROff.clear(); bRW.clear(); bKept.clear(); bRet.clear(); bFrame.clear();
    for k in 0..np { bEsc.push(false); bAll.push(false); bKept.push(false); bRet.push(false); bFrame.push(false); }
    for i in first + np..first + n {
        o: IROp = p.code[i].op;
        if (o != IROp.PtrStore && o != IROp.AggCopy && o != IROp.AggZero && o != IROp.Store && o != IROp.ArrStore
            && o != IROp.Ret && o != IROp.Call && o != IROp.CallIndirect && o != IROp.Asm && o != IROp.Atomic
            && o != IROp.MemCopy) { continue; }
        in: Instr = p.code.get(i);
        if (o == IROp.PtrStore) {
            writeThrough(in.a, base, nt, in.imm, kindWidthOf(in.kind));
            if (!in.bIsImm && frameAddr(p, in.a, base, nt, 0)) { escapeAs(in.b, base, nt, 3); }
            else if (!in.bIsImm) { escape(in.b, base, nt); }
        } else if (o == IROp.AggCopy || o == IROp.AggZero) {
            writeThrough(in.a, base, nt, 0, in.imm);
        } else if (o == IROp.MemCopy) {
            // The destination range alone, from `a` on: its length is a value the program computes.
            writeAll(in.a, base, nt);
        } else if (o == IROp.Store) {
            if (in.isGlobal) { bWild = true; escape(in.a, base, nt); }
            else { escapeAs(in.a, base, nt, 3); }
        } else if (o == IROp.ArrStore) {
            if (in.isGlobal) { bWild = true; }
            if (!in.bIsImm && in.isGlobal) { escape(in.b, base, nt); }
            else if (!in.bIsImm) { escapeAs(in.b, base, nt, 3); }
        } else if (o == IROp.Ret) {
            // Handing back the hidden result pointer, as the convention has it, is no escape: a
            // direct call does not read it (`lower.k` gives such a call no destination).
            r: long = in.a - base;
            sretOnly: bool = hasSret && r >= 0 && r < nt && pvMask.get(r) == 1 && !pvOther.get(r);
            if (!sretOnly) { escapeBack(in.a, base, nt); }
        } else if (o == IROp.Call) {
            s: long = fxOfCallee(p, in.name);
            if (s < 0 || fxParams(s) != in.argCount) {
                bWild = true;
                byConventions(p, in, base, nt);
                continue;
            }
            if (fxWild(s)) { bWild = true; }
            for k in 0..in.argCount {
                t: Temp = p.args.get(in.firstArg + k);
                if (fxKept(s, k)) { escape(t, base, nt); }
                else if (fxEscapes(s, k)) { escapeAs(t, base, nt, 0); }
                if (fxAllOver(s, k)) { writeAll(t, base, nt); continue; }
                for j in 0..fxRangeCount(s, k) { writeThrough(t, base, nt, fxRangeOff(s, k, j), fxRangeW(s, k, j)); }
            }
        } else if (o == IROp.Atomic) {
            // Past an atomic, what another thread wrote may show, so a call to this function ends
            // whatever its caller knows of memory another thread can reach, as a wild write does.
            // It writes the word it is handed (all but a load), and a value it stores is stored.
            bWild = true;
            if (in.imm != BI_ATOMIC_LOAD) { writeThrough(in.a, base, nt, 0, kindWidthOf(in.kind)); }
            if (!in.bIsImm) { escape(in.b, base, nt); }
            for k in 0..in.argCount { escape(p.args.get(in.firstArg + k), base, nt); }
        } else if (o == IROp.CallIndirect) {
            bWild = true;
            escape(in.a, base, nt);
            byConventions(p, in, base, nt);
        } else if (o == IROp.Asm) {
            bWild = true;
            escape(in.a, base, nt);
            for k in 0..in.argCount { escape(p.args.get(in.firstArg + k), base, nt); writeAll(p.args.get(in.firstArg + k), base, nt); }
            for k in 0..in.pieceCount { escape(p.asmVals.get(in.firstPiece + k), base, nt); writeAll(p.asmVals.get(in.firstPiece + k), base, nt); }
        }
    }
    // An address derived from a parameter, kept where this walk loses it, may be what a wild write
    // goes through (read back out of a frame slot, a global, a callee's keeping): the parameter
    // may be written anywhere.
    if (bWild) { for k in 0..np { if (bKept.get(k) || bFrame.get(k)) { bAll.set(k, true); } } }
    // Into the tables.
    s: long = gFxWild.len();
    gFxWild.push(bWild);
    gFxPFirst.push(gFxEsc.len());
    gFxPCount.push(np);
    for k in 0..np {
        gFxEsc.push(bEsc.get(k));
        gFxAll.push(bAll.get(k));
        gFxKept.push(bKept.get(k));
        gFxRet.push(bRet.get(k));
        gFxRFirst.push(gFxROff.len());
        rc: long = 0;
        if (!bAll.get(k)) {
            for j in 0..bRP.len() {
                if (bRP.get(j) == k) { gFxROff.push(bROff.get(j)); gFxRW.push(bRW.get(j)); rc = rc + 1; }
            }
        }
        gFxRCount.push(rc);
    }
    gFxCount = gFxCount + 1;
    return s;
}

// Fold one definition into temp r's provenance; whether it grew.
local defineFrom inout p:IRProgram ix:long base:long nt:long names:Vec<Sym> byVal:Vec<bool> r:long -> bool {
    o: IROp = p.code[ix].op;
    m: long = 0;
    st: long = 0;
    off: long = 0;
    other: bool = false;
    if (o == IROp.Load) {
        k: long = -1;
        if (!p.code[ix].isGlobal) { k = indexIn(names, p.code[ix].name); }
        if (k >= 0 && (p.code[ix].paramSeed || !byVal.get(k))) { m = 1 << k; st = 1; }
        else if (k >= 0) { m = 1 << k; st = 2; other = true; }   // the copy's slot, read by name
        else { other = true; }
    } else if (o == IROp.Mov) {
        a: long = p.code[ix].a - base;
        if (a >= 0 && a < nt) { m = pvMask.get(a); st = pvState.get(a); off = pvOff.get(a); other = pvOther.get(a); }
        else { other = true; }
    } else if (o == IROp.Add || o == IROp.Sub) {
        // An offset is followed through a constant added or taken away.
        in: Instr = p.code.get(ix);
        a: long = in.a - base;
        b: long = -1;
        if (!in.bIsImm) { b = in.b - base; }
        aIn: bool = a >= 0 && a < nt;
        bIn: bool = b >= 0 && b < nt;
        if (aIn) { m = pvMask.get(a); other = pvOther.get(a); }
        else if (in.a != NO_TEMP) { other = true; }
        if (bIn) { m = m | pvMask.get(b); other = other || pvOther.get(b); }
        else if (!in.bIsImm && in.b != NO_TEMP) { other = true; }
        if (m != 0) {
            st = 2;
            c: long = 0;
            known: bool = false;
            if (in.bIsImm) { c = in.bImm; known = true; }
            else if (bIn && pvMask.get(b) == 0 && constOf(p, in.b, base, nt)) { c = gFxConst; known = true; }
            if (known && aIn && pvState.get(a) == 1) {
                st = 1;
                if (o == IROp.Add) { off = pvOff.get(a) + c; } else { off = pvOff.get(a) - c; }
            } else if (o == IROp.Add && aIn && pvMask.get(a) == 0 && bIn && pvState.get(b) == 1
                       && constOf(p, in.a, base, nt)) {
                st = 1;
                off = pvOff.get(b) + gFxConst;
            }
        }
    } else if (o == IROp.Call || o == IROp.CallIndirect) {
        // A result may be an address into what the callee was handed and hands back.
        other = true;
        s: long = -1;
        if (o == IROp.Call) { s = fxOfCallee(p, p.code[ix].name); }
        known: bool = s >= 0 && fxParams(s) == p.code[ix].argCount;
        fa: long = p.code[ix].firstArg;
        for q in 0..p.code[ix].argCount {
            if (known && !fxRet(s, q)) { continue; }
            if (!known && !resultHoldsAddress(p.code[ix].kind)) { break; }
            a: long = p.args.get(fa + q) - base;
            if (a >= 0 && a < nt) { m = m | pvMask.get(a); }
        }
        if (m != 0) { st = 2; }
    } else if (o == IROp.AddrOf) {
        if (p.code[ix].isGlobal) { other = true; }
    } else if (o == IROp.AggSlot || o == IROp.Const || isCompare(o)) {
        // the frame, or no address at all
    } else if (isArithOp(o) || o == IROp.Convert || o == IROp.BNot) {
        // Whatever an address goes through, it is still the same object's, at an offset unknown.
        in: Instr = p.code.get(ix);
        a: long = in.a - base;
        if (a >= 0 && a < nt) { m = pvMask.get(a); other = pvOther.get(a); }
        else if (in.a != NO_TEMP) { other = true; }
        if (!in.bIsImm && in.b != NO_TEMP && o != IROp.Convert && o != IROp.BNot) {
            b: long = in.b - base;
            if (b >= 0 && b < nt) { m = m | pvMask.get(b); other = other || pvOther.get(b); }
            else { other = true; }
        }
        if (m != 0) { st = 2; }
    } else {
        // A load, a call's result, a global's or a string's address, a function's.
        other = true;
    }
    grew: bool = false;
    if ((pvMask.get(r) | m) != pvMask.get(r)) { pvMask.set(r, pvMask.get(r) | m); grew = true; }
    if (other && !pvOther.get(r)) { pvOther.set(r, true); grew = true; }
    if (st != 0) {
        old: long = pvState.get(r);
        if (old == 0) { pvState.set(r, st); pvOff.set(r, off); grew = true; }
        else if (old == 1 && (st == 2 || off != pvOff.get(r))) { pvState.set(r, 2); grew = true; }
    }
    return grew;
}

// A value of the function stored or handed on where it is no longer followed: each parameter it
// derives from escapes, kept past the call.
local escape t:Temp base:long nt:long -> void { escapeAs(t, base, nt, 1); }
// A value handed back as the result: an escape, but one the caller follows (`fxRet`).
local escapeBack t:Temp base:long nt:long -> void { escapeAs(t, base, nt, 2); }
// An escape, and how: 1 kept past the call (`bKept`), 2 handed back (`bRet`), 3 stored in this
// function's own frame (`bFrame`), 0 none of those (handed to a callee that hands it back, which the
// call's result then carries).
local escapeAs t:Temp base:long nt:long how:long -> void {
    r: long = t - base;
    if (t == NO_TEMP || r < 0 || r >= nt) { return; }
    m: long = pvMask.get(r);
    for k in 0..bEsc.len() {
        if ((m & (1 << k)) == 0) { continue; }
        bEsc.set(k, true);
        if (how == 1) { bKept.set(k, true); }
        else if (how == 2) { bRet.set(k, true); }
        else if (how == 3) { bFrame.set(k, true); }
    }
}

// Whether `t` is an address in this function's own frame: a slot's, plus a constant.
local frameAddr inout p:IRProgram t:Temp base:long nt:long depth:long -> bool {
    r: long = t - base;
    if (t == NO_TEMP || r < 0 || r >= nt || depth > 16 || pvDefs.get(r) != 1 || pvDefAt.get(r) < 0) { return false; }
    ix: long = pvDefAt.get(r);
    o: IROp = p.code[ix].op;
    if (o == IROp.AggSlot) { return true; }
    if (o == IROp.AddrOf) { return !p.code[ix].isGlobal && p.code[ix].name != NO_SYM; }
    if (o == IROp.Mov || o == IROp.Convert || ((o == IROp.Add || o == IROp.Sub) && p.code[ix].bIsImm)) {
        return frameAddr(p, p.code[ix].a, base, nt, depth + 1);
    }
    return false;
}

// A write of `w` bytes at `[t + off]`.
local writeThrough t:Temp base:long nt:long off:long w:long -> void {
    r: long = t - base;
    if (t == NO_TEMP || r < 0 || r >= nt) { bWild = true; return; }
    if (pvOther.get(r)) { bWild = true; }
    m: long = pvMask.get(r);
    if (m == 0) { return; }
    for k in 0..bEsc.len() {
        if ((m & (1 << k)) == 0 || bAll.get(k)) { continue; }
        if (pvState.get(r) != 1 || w <= 0) { bAll.set(k, true); continue; }
        at: long = pvOff.get(r) + off;
        dup: bool = false;
        have: long = 0;
        for j in 0..bRP.len() {
            if (bRP.get(j) != k) { continue; }
            have = have + 1;
            if (bROff.get(j) <= at && at + w <= bROff.get(j) + bRW.get(j)) { dup = true; }
        }
        if (dup) { continue; }
        if (have >= MAX_RANGES) { bAll.set(k, true); continue; }
        bRP.push(k);
        bROff.push(at);
        bRW.push(w);
    }
}

// A write anywhere in what `t` points into.
local writeAll t:Temp base:long nt:long -> void {
    r: long = t - base;
    if (t == NO_TEMP || r < 0 || r >= nt) { return; }
    if (pvOther.get(r)) { bWild = true; }
    m: long = pvMask.get(r);
    for k in 0..bAll.len() { if ((m & (1 << k)) != 0) { bAll.set(k, true); } }
}

// `t`'s one definition is a constant, left in `gFxConst`.
local var gFxConst: long = 0;
local constOf inout p:IRProgram t:Temp base:long nt:long -> bool {
    r: long = t - base;
    if (t == NO_TEMP || r < 0 || r >= nt || pvDefs.get(r) != 1 || !pvIsConst.get(r)) { return false; }
    gFxConst = pvConst.get(r);
    return true;
}

local namedIn names:Vec<Sym> n:Sym -> bool { return n != NO_SYM && indexIn(names, n) >= 0; }
local indexIn names:Vec<Sym> n:Sym -> long {
    if (n == NO_SYM) { return -1; }
    for k in 0..names.len() { if (names.get(k) == n) { return k; } }
    return -1;
}

local isArithOp o:IROp -> bool {
    return o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.Div || o == IROp.Mod
        || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor || o == IROp.Shl || o == IROp.Shr;
}

local kindWidthOf k:Lit -> long {
    w: long = typeInfo(k).size;
    if (w < 1 || w > 8) { return 8; }
    if (w == 3) { return 4; }
    if (w > 4) { return 8; }
    return w;
}

local fillL inout v:Vec<long> n:long x:long -> void {
    if (v.len() > n) { v.truncate(n); }
    for i in 0..v.len() { v.set(i, x); }
    while (v.len() < n) { v.push(x); }
}
local fillB inout v:Vec<bool> n:long x:bool -> void {
    if (v.len() > n) { v.truncate(n); }
    for i in 0..v.len() { v.set(i, x); }
    while (v.len() < n) { v.push(x); }
}

// ─── the `.klib`'s EFFECTS chunk ─────────────────────────────────────────────

// After `flow.k`, in a package build: every function's summary, kept by name for the chunk.
local var gFxOutName: Vec<Sym> = vec![];
local var gFxOutId: Vec<long> = vec![];

pub fxNoteExports inout p:IRProgram -> void {
    if (!gFxReady) { fxBegin(p); }
    for f in 0..p.funcs.len() {
        fn: IRFunc = p.funcs.get(f);
        if (fn.imported || fn.instrCount == 0) { continue; }
        if (!fn.isPub && !gInstanceFp.has(nameOf(fn.name))) { continue; }
        s: long = fxOfFunction(p, f);
        if (s < 0) { continue; }
        gFxOutName.push(fn.name);
        gFxOutId.push(s);
    }
}

// The chunk: each exported function's summary, under the label a dependent calls it by.
pub writeEffectsChunk inout out:Encoder -> void {
    exported: HashMap<str, bool>;
    for s in gExportedSyms { exported.put(s, true); }
    inst: HashMap<str, bool>;
    for k in 0..gExportedInst.len() { inst.put(nameOf(gExportedInst.get(k)), true); }
    labels: Vec<Sym>;
    ids: Vec<long>;
    for k in 0..gFxOutName.len() {
        n: str = nameOf(gFxOutName.get(k));
        l: str = "";
        if (inst.has(n)) { l = instanceAlias(n); }
        else if (exported.has(fnLabel(n))) { l = fnLabel(n); }
        else { continue; }
        labels.push(intern(l));
        ids.push(gFxOutId.get(k));
    }
    out.putLen(labels.len());
    for k in 0..labels.len() {
        s: long = ids.get(k);
        labels.get(k).encode(out);
        gFxWild.get(s).encode(out);
        out.putLen(fxParams(s));
        for j in 0..fxParams(s) {
            fxEscapes(s, j).encode(out);
            fxAllOver(s, j).encode(out);
            out.putLen(fxRangeCount(s, j));
            for r in 0..fxRangeCount(s, j) { out.putVarint(fxRangeOff(s, j, r)); out.putVarint(fxRangeW(s, j, r)); }
        }
    }
}

// A dependency's chunk, its names read through the string table already set up. The first
// summary under a label wins: a label belongs to one package.
pub readEffectsChunk inout c:Decoder -> void {
    k: long = c.getLen();
    while (k > 0 && c.ok()) {
        label: Sym = Sym.decode(c);
        s: long = gFxWild.len();
        gFxWild.push(bool.decode(c));
        np: long = c.getLen();
        gFxPFirst.push(gFxEsc.len());
        gFxPCount.push(np);
        for j in 0..np {
            esc: bool = bool.decode(c);
            gFxEsc.push(esc);
            gFxAll.push(bool.decode(c));
            // The chunk does not say how a parameter escapes: either way, then.
            gFxKept.push(esc);
            gFxRet.push(esc);
            rc: long = c.getLen();
            gFxRFirst.push(gFxROff.len());
            gFxRCount.push(rc);
            for r in 0..rc { gFxROff.push(c.getVarint()); gFxRW.push(c.getVarint()); }
        }
        if (!gFxLabel.has(nameOf(label))) { gFxLabel.put(nameOf(label), s); }
        k = k - 1;
    }
}

// A call whose callee's summary is not known: what it does with each argument, by its callee's
// conventions (`callLends`, `callMayWrite`). An argument it is lent is never kept, and is written
// only where the parameter may write; any other argument escapes and may be written all over.
local byConventions inout p:IRProgram in:Instr base:long nt:long -> void {
    imm: long = in.imm;
    if (gLentOff) { imm = 0; }
    for k in 0..in.argCount {
        t: Temp = p.args.get(in.firstArg + k);
        if (!callLends(imm, k)) { escape(t, base, nt); }
        if (callMayWrite(imm, k)) { writeAll(t, base, nt); }
    }
}
