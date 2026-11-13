// The IR as text, one instruction per line.
//
// For reading and for regression: temp numbers are printed as they are, so this is only
// comparable against itself, not against the C++ compiler, the two number their temps
// differently. What it is for is seeing that a lowering is the shape it should be.
#include <ir>
#include <parse::types>
#include <support::compiler>
#include <stdlib::{fmt, string, vec, map, option}>

pub dumpIR p:IRProgram inout out:String -> void {
    for f in 0..p.funcs.len() {
        fn: IRFunc = p.funcs.get(f);
        out.pushStr("fn ");
        out.pushStr(nameOf(fn.name));
        out.push('\n');
        seen: HashMap<long, long>;
        for k in 0..fn.instrCount {
            dumpInstr(p, out, &seen, p.code.get(fn.firstInstr + k));
        }
    }
}

// A temp's number within this function: the order it was first mentioned in, not the id the
// lowerer happened to hand it. The two compilers count from different places.
local temp inout out:String inout seen:HashMap<long, long> t:Temp -> void {
    if (t == NO_TEMP) { out.pushStr("_"); return; }
    hit: Option<long> = seen.find(t);
    n: long = seen.len();
    match hit { Some(v) { n = v; } None { seen.put(t, n); } }
    out.push('t');
    out.pushLong(n);
}

pub dumpInstr p:IRProgram inout out:String inout seen:HashMap<long, long> in:Instr -> void {
    // An instruction the optimizer deleted. It stays in the list so no function's run moves, and
    // printing it would be printing something the emitter will not emit.
    if (in.op == IROp.Nop) { return; }
    if (in.op == IROp.Label) {
        out.pushStr(nameOf(in.name));
        out.pushStr(":\n");
        return;
    }
    out.pushStr("  ");
    if (in.dst != NO_TEMP) { temp(out, seen, in.dst); out.pushStr(" = "); }
    out.pushStr(irOpName(in.op));

    if (in.op == IROp.Const) { out.push(' '); out.pushLong(in.imm); }
    // Which scratch slot: they are numbered program-wide, and two of one number are one place.
    else if (in.op == IROp.AggSlot) { out.pushStr(" #"); out.pushLong(in.imm); }
    else if (in.op == IROp.Load || in.op == IROp.Store || in.op == IROp.AddrOf) {
        out.push(' ');
        out.pushStr(nameOf(in.name));
        // A prologue seed, not an instruction the source asked for: this compiler opens a body by
        // loading each parameter out of its own slot, where the C++ one keeps a separate parameter
        // list. Marked because comparing the two by shape has to normalize those away, and the
        // marker is the only thing that says exactly which loads they are: inferring them from
        // "the leading run of loads of distinct names" guesses wrong for a body that opens by
        // reading a local. It is dump text that nothing reads back, so it cannot make two runs of
        // this compiler differ.
        if (in.paramSeed) { out.pushStr(" (param)"); }
        if (in.op == IROp.Store) { out.pushStr(" <- "); temp(out, seen, in.a); }
    }
    else if (in.op == IROp.Call || in.op == IROp.CallIndirect) {
        out.push(' ');
        out.pushStr(nameOf(in.name));
        out.push('(');
        for k in 0..in.argCount {
            if (k > 0) { out.pushStr(", "); }
            temp(out, seen, p.args.get(in.firstArg + k));
        }
        out.push(')');
    }
    else if (in.op == IROp.Jcc) {
        // Jumps when the comparison holds: `jcc L if t3 cmplt t5`.
        out.push(' ');
        out.pushStr(nameOf(in.name));
        out.pushStr(" if ");
        // A float branch that jumps when the comparison does not hold (`Opt.fuseBranches`).
        if (in.imm == 1 && (in.kind == Lit.Float || in.kind == Lit.Double)) { out.pushStr("not "); }
        temp(out, seen, in.a);
        out.push(' ');
        out.pushStr(irOpName(in.cmpOp));
        out.push(' ');
        if (in.bIsImm) { out.push('#'); out.pushLong(in.bImm); } else { temp(out, seen, in.b); }
    }
    else if (isBranch(in.op)) {
        out.push(' ');
        out.pushStr(nameOf(in.name));
        if (in.a != NO_TEMP) { out.pushStr(" if !"); temp(out, seen, in.a); }
    }
    else if (in.op == IROp.PtrLoad || in.op == IROp.PtrStore) {
        out.pushStr(" [");
        temp(out, seen, in.a);
        if (in.imm != 0) { out.pushStr(" + "); out.pushLong(in.imm); }
        out.push(']');
        if (in.op == IROp.PtrStore) {
            out.pushStr(" <- ");
            if (in.bIsImm) { out.push('#'); out.pushLong(in.bImm); } else { temp(out, seen, in.b); }
        }
    }
    else {
        if (in.a != NO_TEMP) { out.push(' '); temp(out, seen, in.a); }
        if (in.bIsImm) { out.pushStr(", #"); out.pushLong(in.bImm); }
        else if (in.b != NO_TEMP) { out.pushStr(", "); temp(out, seen, in.b); }
    }

    if (in.kind != Lit.Void) {
        out.pushStr("  :");
        out.pushStr(typeName(in.kind));
    }
    out.push('\n');
}

// The opcode's spelling, as a table built once and indexed by the opcode. An opcode with no entry
// reads as `?`, which is what an op added to the IR and forgotten here looks like in a dump.
local gIrOpNames: Vec<str> = irOpNames();

local irOpNames -> Vec<str> {
    t: Vec<str>;
    i: long = 0;
    while (i <= (IROp.Nop as long)) { t.push("?"); i = i + 1; }
    t.set(IROp.Const as long,        "const");
    t.set(IROp.Load as long,         "load");
    t.set(IROp.Store as long,        "store");
    t.set(IROp.Mov as long,          "mov");
    t.set(IROp.Add as long,          "add");
    t.set(IROp.Sub as long,          "sub");
    t.set(IROp.Mul as long,          "mul");
    t.set(IROp.Div as long,          "div");
    t.set(IROp.Mod as long,          "mod");
    t.set(IROp.BAnd as long,         "and");
    t.set(IROp.BOr as long,          "or");
    t.set(IROp.BXor as long,         "xor");
    t.set(IROp.Shl as long,          "shl");
    t.set(IROp.Shr as long,          "shr");
    t.set(IROp.BNot as long,         "not");
    t.set(IROp.CmpEq as long,        "cmpeq");
    t.set(IROp.CmpNe as long,        "cmpne");
    t.set(IROp.CmpLt as long,        "cmplt");
    t.set(IROp.CmpGt as long,        "cmpgt");
    t.set(IROp.CmpLe as long,        "cmple");
    t.set(IROp.CmpGe as long,        "cmpge");
    t.set(IROp.Convert as long,      "convert");
    t.set(IROp.Call as long,         "call");
    t.set(IROp.CallIndirect as long, "calli");
    t.set(IROp.Ret as long,          "ret");
    t.set(IROp.RetVoid as long,      "retvoid");
    t.set(IROp.Label as long,        "label");
    t.set(IROp.Jmp as long,          "jmp");
    t.set(IROp.Jz as long,           "jz");
    t.set(IROp.Jcc as long,          "jcc");
    t.set(IROp.Nop as long,          "nop");
    t.set(IROp.Asm as long,          "asm");
    t.set(IROp.ArrLoad as long,      "arrload");
    t.set(IROp.ArrStore as long,     "arrstore");
    t.set(IROp.AddrOf as long,       "addrof");
    t.set(IROp.StrAddr as long,      "straddr");
    t.set(IROp.PtrLoad as long,      "ptrload");
    t.set(IROp.PtrStore as long,     "ptrstore");
    t.set(IROp.AggCopy as long,      "aggcopy");
    t.set(IROp.AggZero as long,      "aggzero");
    t.set(IROp.Bounds as long,       "bounds");
    t.set(IROp.StrLitVal as long,    "strlit");
    t.set(IROp.AggSlot as long,      "aggslot");
    t.set(IROp.VtableAddr as long,   "vtable");
    t.set(IROp.FnAddr as long,       "fnaddr");
    return t;
}

pub irOpName op:IROp -> str { return gIrOpNames.get(op as long); }
