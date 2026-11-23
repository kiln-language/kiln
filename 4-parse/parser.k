// Tokens to a syntax tree: recursive descent, one token of lookahead.
//
// Expressions are built by `insertOp`, which splices a new operator in where its precedence says
// it belongs rather than by a function per level. Names resolve as they are parsed: a local is
// renamed on declaration, and a top-level name is qualified with the module that declared it.
#include <{ast, astdump, diag, quoter, regops, registry, upstream, types}>
#include <lex::{lexer, token}>
#include <stdlib::{chars, path, pathbuf, fmt, map, option, recover, string, vec}>
#include <support::compiler>

// "no statement yet", for a methods block that has not produced one.
pub NO_STMT: long = -1;

// A name and what it resolves to, in one scope.
// `isArray`: a fixed array, `xs: [T; N]`, whose kind is its element's: what `for x in xs` reads.
pub struct Binding { name: Sym, renamed: Sym, kind: Lit, structName: Sym, isArray: bool }

// Where a template's parameter list is, for holding `Name<...>` to it: the registry's run
// (`first`), or, while the template's own declaration is being read, the parser's copy (`own`).
pub struct TplRef { known: bool, own: bool, first: long, count: long }

// The sum type a `match` is reading, as whichever of three registrations answers for it.
//
// A concrete enum is in the enum table. An instance such as `Option<long>` is not a type yet at
// parse time, because monomorphization runs later, so what it holds is read from the template
// with the request's arguments substituted. And inside `methods Option<T>` the value's type is the
// template itself, where a payload stays the parameter it is and the monomorph pass substitutes
// it along with everything else.
pub struct SumInfo { owner: Sym, enumAt: long, tmplAt: long, reqAt: long, backing: Lit }

// A place's type as the parser knows it (see `Parser.placeTy`): what `for x in xs` reads.
pub struct PlaceTy { kind: Lit, name: Sym, isArray: bool, ok: bool }

// What `for x in xs` walks.
local FOR_NONE: long = 0;
local FOR_SLICE: long = 2;
local FOR_ARRAY: long = 3;
local FOR_ITER: long = 4;
local FOR_VIEW: long = 5;      // a type implementing `AsSlice<T>`: walked as the slice it views

// `builtin` was read before the declaration: `parseFunctionDef` holds it to a builtin's shape.
local FN_BUILTIN_DECL: long = 128;

// One variable a closure body names from outside itself. A scalar is captured by pointer, so a
// write inside the closure is a write to the original; a struct is captured as a borrow; a `str`,
// a slice or a fn is copied, being a view or a value already.
pub struct Capture { level: long, name: Sym, value: NodeId, kind: Lit, structName: Sym,
                     byPtr: bool }

// Where a `macro` declaration was met, to be parsed once the whole program has been: the
// lexer's position and the token in hand, so the declaration is re-read from the same source
// with its own line numbers. A macro is written against `ast`'s `Node`, and `ast` is built on
// `Vec`, so `vec.k` declares its literal before `ast` is parsed and the body can only be read
// afterwards. Deferring the whole declaration, signature and body, is what lets a module name a
// type that arrives later, for the one construct that needs to.
pub struct MacroSnap { name: Sym, pos: long, line: long, col: long, file: Sym, pkg: Sym,
                       cur: Token, peeked: Token, hasPeeked: bool, vis: Vis, curPos: long, peekPos: long,
                       // The module's own text, which the lexer is put back on; the module's index in
                       // the scan; and, for a macro a `.klib` brought already parsed, its statement
                       // (-1 for one read from source).
                       src: str, mod: long, loaded: long }

// A name met while a module is read that must turn out to be declared, asked at the module's end,
// where one declared below its use has been read too: the trait of a `methods X for T`
// (`isType` false), or the template of a `T<args>` (`isType` true).
pub struct ImplCheck { trait: Sym, owner: Sym, line: long, col: long, file: Sym, isType: bool }

// Where the parser is in its text: the lexer and the token or two in hand.
pub struct Cursor { lx: Lexer, cur: Token, peeked: Token, hasPeeked: bool, curPos: long, peekPos: long }

// Where a top-level declaration began, and how far everything it can add to reached then: what
// the parser cuts back to when an error cuts the declaration short (`rewindTo`). The lists are
// lengths; the rest is the state a declaration starts in, which the error may have left changed.
pub struct ParseMark {
    ast: AstMark, reg: RegMark, ops: OpsMark, startPos: long, gPos: long,
    pendingMacros: long, tplBounds: long, scopes: long, scopeStart: long, implChecks: long,
    pendingInits: long, closureBound: long, closureName: long, captures: long,
    closureFile: str, closureSeq: long, fnReturnsAdded: long, pending: long, typeVars: long,
    lenVars: long, tplParams: long, selfParams: long, selfInfo: long, pageIds: long,
    tryHole: long, toOrder: long, contPre: long,
    inImpl: bool, uniq: long, matchSeq: long, forSeq: long, loopDepth: long, fnDepth: long,
    implMangled: Sym, noCast: long, inPointee: long, quoteDepth: long, unsafeDepth: long,
    vis: Vis, varDecl: bool, boundFirst: long, boundCount: long, selfTpl: Sym, lenArgOk: bool,
    typeVarUses: long, plainBody: bool, blanketVar: Sym, blanketAs: Sym, retTy: TypeRef,
    retOk: bool, toMark: long, toImpure: bool, toCond: long, toLhs: long, contIf: long,
    retNever: bool, fnAttrs: long, lastStmt: long
}

pub struct Parser {
    lx:  Lexer,
    cur: Token,
    pendingMacros: Vec<MacroSnap>,

    ast: Ast,

    // The bounds a generic type's header declared, held between reading the header and
    // recording the template. One list at a time: a template's header is finished before the
    // next one is read.
    tplBounds: Vec<MethodBound>,
    inImpl: bool,              // inside `methods X for Trait { ... }`

    scopes:  Vec<Binding>,     // a flat stack; `scopeStart` says where each frame begins
    scopeStart: Vec<long>,
    uniq: long,                // makes each shadowing declaration a distinct name
    matchSeq: long,            // names the hidden `$matchN` scrutinee a `match <var>.<field>` binds
    forSeq: long,              // names the hidden `$forpN`/`$fornN`/`$foriN` of a `for x in xs`

    loopDepth: long,           // `break`/`continue` are only valid inside a loop
    fnDepth: long,             // zero at the top level, where a declaration is a global
    implMangled: Sym,          // `Eq_str` while that impl block's methods are being named
    implChecks: Vec<ImplCheck>,// this module's `methods X for T`, each T to be found a trait
    noCast: long,              // nonzero while reading a prefix operator's operand
    // Nonzero while reading a pointee. `next: *Node` inside `struct Node` names the struct being
    // declared, which is not registered yet, and a pointer is 8 bytes whatever it points at, so
    // the name need not resolve for the type to be known.
    inPointee: long,
    quoteDepth: long,          // nonzero inside a `quote { }`, where `@x` is a splice
    pendingInits: Vec<long>,   // a declaration's initializer, waiting to be handed back
    peeked: Token,             // one token of pushback, for `peekNext`
    hasPeeked: bool,
    // The closures being read, innermost last: where each one's own scope begins and what it is
    // called. `captures` holds every open closure's captures at once, tagged with its level.
    closureBound: Vec<long>,
    closureName: Vec<Sym>,
    captures: Vec<Capture>,
    closureSeq: HashMap<str, long>,   // closures read so far, per file: the next one's number
    // Nonzero while reading an `unsafe { }` block or an `unsafe` function's body. A closure
    // written there is the one kind whose body is trusted, since that is where its text stands.
    unsafeDepth: long,
    fnReturns: HashMap<str, Lit>,  // what a already-parsed function returns, for a call's type
    vis: Vis,                  // the visibility keyword the current declaration carried
    varDecl: bool,             // `var` was read before the current top-level declaration
    pending: Vec<long>,        // extra top-level statements a declaration produced
    typeVars: Vec<Sym>,        // the template parameters in scope, if any
    boundFirst: long, boundCount: long,  // the enclosing block's bounds, for every method in it
    // The ones of `typeVars` that are lengths (`N: long`): a length where an array's length or a
    // value goes, never where a type does.
    lenVars: Vec<Sym>,
    // What the last `<...>` header said of each parameter it named: a length or a type, and its
    // default. Read by whoever records the template, right after the header.
    tplParams: Vec<GParamInfo>,
    // The template whose declaration or methods block is being read, with its parameters: inside
    // them `Buf<T>` leaves out a parameter by meaning this instance's own, not its default.
    selfTpl: Sym,
    selfParams: Vec<Sym>,
    selfInfo: Vec<GParamInfo>,
    // Set by `parseGenericArgs` for the argument it is about to read: there, and only there, a
    // type may instead be a length (`Buf<64>`, `Buf<PATH_MAX>`).
    lenArgOk: bool,
    // How many times a template parameter has been named, so a default can be held to naming none.
    typeVarUses: long,
    // Reading a body that is not generic: what a dependent holds a request made there back for
    // (`RequestRec.inBody`).
    plainBody: bool,
    // The page: every top-level statement so far, in order, with the module each belongs to and
    // whether it is a macro read at the end of the page (what a `.klib` records per module). The
    // module being read is `curMod`, its index in the scan.
    pageIds: Vec<long>,
    pageMod: Vec<long>,
    pageDeferred: Vec<bool>,
    curMod: long,
    curPos: long,              // where `cur` begins (`posOf`), and where `peeked` does
    peekPos: long,
    // `methods<T: Integer> T for X`, read once per type the category holds: the parameter's name,
    // and the scalar it stands for in this reading (`parseBlanketMethods`).
    blanketVar: Sym,
    blanketAs: Sym,
    // What the function whose body is being read returns (`retOk`: there is one to say; not in a
    // closure's body), which a `?` returns early as.
    retTy: TypeRef,
    retOk: bool,
    // The `?`s read so far whose statements are not finished: where each stood (the local its Ok
    // value is read through), its operand, and that local's name. A statement takes the ones from
    // where the list stood when it began (`parseStatement`).
    tryHole: Vec<NodeId>,
    tryOperand: Vec<NodeId>,
    tryName: Vec<Sym>,
    // The walk that puts a statement's `?`s in the order they run (`tryOrder`).
    toMark: long,
    toImpure: bool,
    toCond: long,
    toLhs: long,
    toOrder: Vec<long>,
    // `x: T = f()?;`: the declaration and every statement after it in its block go in the `?`'s
    // `else` (the output's side), so the early return is taken before `x` exists (nothing
    // half-made is released on it). The `else` link, and the statements its body starts with,
    // until the block's end is read.
    contIf: long,
    contPre: Vec<long>,
    // What the declaration being read says beyond its signature: `-> never` (`parseRetType`),
    // `builtin` (`fnAttrs` carries the bit until `parseFunctionDef` reads it).
    retNever: bool,
    fnAttrs: long,
    // The statement read last, so that an `=` starting the next one can say what it follows
    // (`{ x } = 1`: a block is not something a store can go to).
    lastStmt: long,
    // Going on past a declaration with an error in it (`parseDeclRecovering`): the type the
    // top-level declaration being read declares, once its name is read; the types of the ones taken
    // back, and whether the declaration being read has named one, which drops it without a report
    // (`dropIfAbandoned`); the module's own cursor while compiler-written text is read in its place
    // (`parseSynthetic`); and the names `fnReturns` gained, in order.
    declName: Sym,
    abandoned: Vec<Sym>,
    usesAbandoned: bool,
    synthSaved: Vec<Cursor>,
    fnReturnsAdded: Vec<Sym>
}

pub parserOf source:str -> Parser {
    l: Lexer = lexerOf(source);
    a: Ast;
    p: Parser = Parser { lx: l, cur: tokenOf(Tok.FileEnd), pendingMacros: vec![], ast: a,
                         tplBounds: vec![], inImpl: false,
                         scopes: vec![], scopeStart: vec![], uniq: 0, matchSeq: 0, forSeq: 0, loopDepth: 0, fnDepth: 0,
                         implMangled: NO_SYM, implChecks: vec![], noCast: 0, inPointee: 0, quoteDepth: 0, pendingInits: vec![], fnReturns: map![],
                         peeked: tokenOf(Tok.FileEnd), hasPeeked: false,
                         closureBound: vec![], closureName: vec![], captures: vec![], closureSeq: map![],
                         unsafeDepth: 0, vis: Vis.Local, varDecl: false,
                         pending: vec![], typeVars: vec![],
                         boundFirst: 0, boundCount: 0,
                         lenVars: vec![], tplParams: vec![], selfTpl: NO_SYM, selfParams: vec![],
                         selfInfo: vec![], lenArgOk: false, typeVarUses: 0, plainBody: false,
                         pageIds: vec![], pageMod: vec![], pageDeferred: vec![], curMod: -1,
                         curPos: 0, peekPos: 0, blanketVar: NO_SYM, blanketAs: NO_SYM , retTy: typeRefOf(Lit.Void), retOk: false,
                         tryHole: vec![], tryOperand: vec![], tryName: vec![], toMark: 0, toImpure: false,
                         toCond: 0, toLhs: 0, toOrder: vec![], contIf: -1, contPre: vec![],
                         retNever: false, fnAttrs: 0, lastStmt: -1,
                         declName: NO_SYM, abandoned: vec![], usesAbandoned: false, synthSaved: vec![],
                         fnReturnsAdded: vec![] };
    p.advance();
    p.pushScope();
    return p;
}

methods Parser {
    // ─── the cursor ──────────────────────────────────────────────────────────

    advance &self -> Token {
        was: Token = self.cur;
        if (self.hasPeeked) { self.cur = self.peeked; self.curPos = self.peekPos; self.hasPeeked = false; }
        else { self.cur = self.lx.next(); self.curPos = self.lexPos(); }
        if (self.abandoned.len() > 0 && self.cur.kind == Tok.Id) { self.noteAbandonedUse(); }
        return was;
    }

    // One token past the current one. A keyword is only a keyword where a keyword can stand, and
    // telling that apart takes two tokens: `match` opens a match statement, but `match: long = 1;`
    // declares a variable called `match`.
    peekNext &self -> Token {
        if (!self.hasPeeked) { self.peeked = self.lx.next(); self.peekPos = self.lexPos(); self.hasPeeked = true; }
        return self.peeked;
    }
    // Where the token the lexer just returned begins.
    lexPos &self -> long { return posOf(self.lx.currentFile, self.lx.tokLine, self.lx.tokCol); }
    // Is the identifier here being declared or assigned, rather than spelling a construct?
    namedHere &self -> bool {
        k: Tok = self.peekNext().kind;
        return k == Tok.Colon || k == Tok.Equals;
    }
    check &self k:Tok -> bool { return self.cur.kind == k; }
    // An identifier with a particular spelling: every keyword is one.
    word &self w:str -> bool {
        return self.cur.kind == Tok.Id && nameOf(self.cur.text) == w;
    }
    eat &self k:Tok -> bool {
        if (self.cur.kind != k) { return false; }
        self.advance();
        return true;
    }
    eatWord &self w:str -> bool {
        if (!self.word(w)) { return false; }
        self.advance();
        return true;
    }
    expect &self k:Tok -> Token {
        if (self.cur.kind != k) {
            self.err(format("expected {}, found {}", describeKind(k), describeTok(self.cur)));
        }
        return self.advance();
    }
    // A syntax error, reported where the current token begins: the token the parser could not
    // use, which is where gcc and rustc point too. Before the first token has a position (a
    // lexer run on raw text), the lexer's own cursor is the best there is.
    err &self msg:String -> void {
        p: long = self.curPos;
        if (p == 0 || posFile(p) == NO_SYM) {
            self.dropIfAbandoned();
            where: str = "";
            if (self.lx.currentFile != NO_SYM) { where = nameOf(self.lx.currentFile); }
            failAtStr(where, self.lx.fileLine, self.lx.charNumber, msg);
        }
        self.errAt(p, msg);
    }
    // A syntax error at position `p`.
    errAt &self p:long msg:String -> void {
        self.dropIfAbandoned();
        failAtStr(nameOf(posFile(p)), posLine(p), posCol(p), msg);
    }
    // A declaration that names a type whose own declaration was taken back is taken back too,
    // without a word: its error may be no more than that one's, met again, and the compile stops
    // after the parse either way. The raise is the parser's own, to the `recover` the declaration
    // is read under (`parseDeclRecovering`).
    dropIfAbandoned &self -> void {
        if (self.usesAbandoned && recoverArmed()) { unsafe { raise(); } }
    }
    // Whether the token just taken is the name of a type a declaration taken back was declaring.
    noteAbandonedUse &self -> void {
        for k in 0..self.abandoned.len() {
            if (self.abandoned.get(k) == self.cur.text) { self.usesAbandoned = true; }
        }
    }

    // `<file>:<line>` for the token being parsed, what a diagnostic says, in the one place a
    // runtime failure gets to say it too: a bounds check reports from the emitted program, long
    // after the compiler that knew the position is gone, so the position travels with the node.
    sourceHere &self -> Sym {
        s: String;
        if (self.lx.currentFile != NO_SYM) { s.pushStr(nameOf(self.lx.currentFile)); }
        else { s.pushStr("<input>"); }
        s.push(':');
        s.pushLong(self.lx.fileLine);
        return internString(s);
    }

    // ─── scopes ──────────────────────────────────────────────────────────────

    pushScope &self -> void { self.scopeStart.push(self.scopes.len()); }
    popScope &self -> void {
        if (self.scopeStart.len() <= 1) { return; }
        at: long = self.scopeStart.pop();
        while (self.scopes.len() > at) { self.scopes.pop(); }
    }

    // Declare `n` in the innermost scope. Shadowing renames rather than nesting a lookup: the
    // later declaration gets a fresh name, so every use downstream names exactly one variable and
    // no phase after this has to think about scope at all.
    declareLocal &self n:Sym kind:Lit structName:Sym -> Sym {
        // Reusing a name a sibling block used is an intent; writing it twice in one block is a
        // mistake, and the rename below would quietly turn it into two variables that both
        // answer to the same spelling. Only this frame is searched: an outer one is the
        // shadowing the rename exists for.
        frame: long = self.scopeStart.get(self.scopeStart.len() - 1);
        j: long = self.scopes.len();
        while (j > frame) {
            j = j - 1;
            if (self.scopes.get(j).name == n) {
                self.err(format("`{}` is already declared in this block", nameOf(n)));
            }
        }
        // A length parameter is a value in the body, so a variable of the same name would make
        // `N` mean two things; monomorphization writes the length over every use of the name.
        if (self.isLenVar(n)) {
            self.err(format("`{}` is a length parameter here, so it cannot also name a variable", nameOf(n)));
        }
        renamed: Sym = n;
        if (self.lookupLocal(n) != NO_SYM) {
            s: String;
            s.pushStr(nameOf(n));
            s.pushStr("$");
            s.pushLong(self.uniq);
            self.uniq = self.uniq + 1;
            renamed = internString(s);
        }
        self.scopes.push(Binding { name: n, renamed: renamed, kind: kind, structName: structName,
                                   isArray: false });
        return renamed;
    }

    // The innermost binding of `n`, or NO_SYM. Searched from the top, so the innermost wins.
    lookupLocal &self n:Sym -> Sym {
        i: long = self.scopes.len();
        while (i > 0) {
            i = i - 1;
            b: Binding = self.scopes.get(i);
            if (b.name == n) { return b.renamed; }
        }
        return NO_SYM;
    }
    bindingOf &self n:Sym -> Binding {
        i: long = self.scopes.len();
        while (i > 0) {
            i = i - 1;
            b: Binding = self.scopes.get(i);
            if (b.name == n) { return b; }
        }
        return Binding { name: NO_SYM, renamed: NO_SYM, kind: Lit.Void, structName: NO_SYM, isArray: false };
    }

    // Where `n` was declared, as an index into the scope stack, or -1.
    bindingIndexOf &self n:Sym -> long {
        i: long = self.scopes.len();
        while (i > 0) {
            i = i - 1;
            if (self.scopes.get(i).name == n) { return i; }
        }
        return NOT_FOUND;
    }

    // If `n` belongs to the scope around the closure being read, record it as a capture and give
    // back the expression that reads it through the closure's own struct: `__cl.x`, or `*__cl.n`
    // for a scalar, which is captured by pointer so a write inside reaches the original.
    //
    // Closures nest, and a variable named by an inner one is captured by every closure between it
    // and its declaration, each from the one around it. The inner closure reads a field of the
    // outer one's struct rather than the original variable, which is no longer in scope where the
    // inner one is built.
    captureOf &self n:Sym -> NodeId {
        lv: long = self.closureBound.len() - 1;
        if (lv < 0) { return NO_NODE; }
        at: long = self.bindingIndexOf(n);
        if (at == NOT_FOUND || at >= self.closureBound.get(lv)) { return NO_NODE; }
        b: Binding = self.scopes.get(at);
        if (b.kind == Lit.Ref && isInoutScalarName(b.structName)) {
            self.err(format("a closure cannot capture `inout` scalar parameter `{}`\nhelp: copy it into a local first, and capture that",
                            nameOf(n)));
        }
        // A scalar is captured by pointer, so a write inside the closure lands on the original;
        // a struct by borrow; anything already a handle (str, slice, trait object, fn) by copy.
        // A backed enum or a distinct type is spelled like a struct but is its integer, so it is
        // a scalar here.
        //
        // A ref needs care, because `&` of a ref hands on the address it holds rather than taking
        // the address of where it is held. A borrow of a struct (`&self`, an `inout` parameter)
        // is captured as that borrow; through a pointer to it, every read would go through one
        // load too many. The `&self` of `methods long`, `methods str` or a backed enum holds the
        // value itself, and a store to it is refused, so the closure holds a copy. A `&T` keeps
        // the pointer: at a scalar `T` it is the scalar, whose address `&` does take.
        held: Binding = b;
        lent: bool = false;
        copied: bool = false;
        if (b.kind == Lit.Ref && b.structName != NO_SYM && !self.isTypeVar(b.structName)
            && !isInoutScalarName(b.structName)) {
            q: str = nameOf(b.structName);
            if (namesScalar(q)) {
                copied = true;
                held.kind = scalarNamed(q);
                held.structName = NO_SYM;
            } else if (namedScalar(Lit.Struct, b.structName)) {
                copied = true;
                held.kind = Lit.Struct;
            } else {
                lent = true;
                // `self` in a generic type's methods is declared with the template's bare name,
                // which monomorphization reads as the instance only inside those methods. The
                // capture struct is a template of its own, so its field names the instance at
                // the block's parameters.
                if (b.structName == self.selfTpl) {
                    none: Vec<TypeRef>;
                    held.structName = self.instanceOf(b.structName, none).name;
                }
            }
        }
        named: bool = b.kind == Lit.Struct && namedScalar(Lit.Struct, b.structName);
        byPtr: bool = (!isAggregate(b.kind) || named) && b.kind != Lit.Fn && !lent && !copied;

        // The outermost closure the declaration is not inside is the first that has to capture it.
        j: long = 0;
        while (at >= self.closureBound.get(j)) { j = j + 1; }

        v: NodeId = self.ast.leafOf(Op.Lvalue, Payload.Name(b.renamed), b.kind, b.structName);
        if (byPtr || lent || b.kind == Lit.Struct) { v = self.ast.unary(Op.AddressOf, v, Lit.Ptr); }
        while (j <= lv) { v = self.captureAt(j, n, held, byPtr, v); j = j + 1; }
        if (byPtr) { return self.ast.unary(Op.Deref, v, b.kind); }
        return v;
    }

    // The type a capture's field holds: a pointer to a scalar, a borrow of a struct, or the value
    // itself for a handle or a copied `&self`.
    captureField &self kind:Lit sn:Sym byPtr:bool -> TypeRef {
        if (byPtr) { return TypeRef { base: Lit.Ptr, name: intern(typeMangleName(kind, sn)) }; }
        if (kind == Lit.Struct && !namedScalar(Lit.Struct, sn)) { return TypeRef { base: Lit.Ref, name: sn }; }
        return TypeRef { base: kind, name: sn };
    }

    // Record `n` among closure level `lv`'s captures unless it is already there, and return the
    // field access that reads it inside that closure. That access is also what the closure one
    // level further in stores, since by then the variable itself is out of scope.
    captureAt &self lv:long n:Sym b:Binding byPtr:bool v:NodeId -> NodeId {
        seen: bool = false;
        for k in 0..self.captures.len() {
            c: Capture = self.captures.get(k);
            if (c.level == lv && c.name == n) { seen = true; }
        }
        if (!seen) {
            self.captures.push(Capture { level: lv, name: n, value: v, kind: b.kind,
                                         structName: b.structName, byPtr: byPtr });
        }
        recv: NodeId = self.ast.leafOf(Op.Lvalue, Payload.Name(intern("__cl")), Lit.Ref,
                                       self.closureName.get(lv));
        self.ast.fields.push(FieldNode { base: recv, name: n });
        f: TypeRef = self.captureField(b.kind, b.structName, byPtr);
        return self.ast.leafOf(Op.FieldAccess, Payload.Field(self.ast.fields.len() - 1), f.base, f.name);
    }

    // Level `lv`'s captures, in the order they were met, taken out of the flat list. Every other
    // closure still open keeps its own.
    takeCaptures &self lv:long -> Vec<Capture> {
        out: Vec<Capture>;
        rest: Vec<Capture>;
        for k in 0..self.captures.len() {
            c: Capture = self.captures.get(k);
            if (c.level == lv) { out.push(c); } else { rest.push(c); }
        }
        self.captures = rest;
        return out;
    }

    // A closure (`|x: T| expr`, `|x: T| { ... }` or `|| ...`) is desugared here into the three
    // things it actually is: a struct holding one field per captured variable, a `call` method
    // whose body is the closure's with each capture read through that struct, and a literal
    // building it. The struct implements the `Fn` trait for its arity, so a closure goes wherever
    // a bound or a trait object asks for one, and nothing downstream knows closures exist.
    parseClosure &self -> NodeId {
        // Numbered within the file it is written in, and marked with that file's path: the name
        // is a symbol, and a package compiled on its own must give a closure the same one its
        // dependents give it when they parse the same file among different neighbours. A count
        // across the whole program would differ between the two; the stem alone would not tell
        // apart two modules of one name in two packages.
        file: str = nameOf(self.lx.currentFile);
        seq: long = 0;
        had: Option<long> = self.closureSeq.find(file);
        match had { Some(n) { seq = n; } None { } }
        self.closureSeq.put(file, seq + 1);
        base: Sym = self.qualify(keepString(format("$closure{}_{}", seq, strHash(file) & 0xFFFFFFFF)));
        lv: long = self.closureBound.len();
        self.closureBound.push(self.scopes.len());
        self.closureName.push(base);
        self.pushScope();

        params: Vec<long> = self.parseClosureParams();

        ret: TypeRef = TypeRef { base: Lit.Void, name: NO_SYM };
        explicit: bool = false;
        if (self.eat(Tok.Arrow)) { ret = self.parseTypeRef(); explicit = true; }

        body: long = 0;
        if (self.check(Tok.LeftCurly)) {
            body = self.parseBlock();
            if (!explicit) { ret = self.firstReturnType(body); }
        } else {
            // An expression body is a `return` of that expression, and the closure returns what
            // that expression is.
            v: NodeId = self.parseExprHere();
            if (!explicit) {
                e: Expr = self.ast.expr(v);
                ret = TypeRef { base: e.kind, name: e.structName };
            }
            self.ast.returns.push(ReturnNode { value: v });
            ids: Vec<long>;
            ids.push(self.ast.addStmt(StmtKind.Return, self.ast.returns.len() - 1));
            body = self.ast.addBlock(ids);
        }
        self.popScope();
        self.closureBound.pop();
        self.closureName.pop();
        caps: Vec<Capture> = self.takeCaptures(lv);

        self.declareClosureStruct(base, caps);
        self.declareClosureCall(base, params, ret, explicit, body);
        return self.closureLiteral(base, caps);
    }

    // What a block body returns: the first `return` it reaches, wherever it is nested. A closure
    // whose body returns nothing is a `void` one, as most closures written for their effect are.
    firstReturnType &self b:long -> TypeRef {
        none: TypeRef = TypeRef { base: Lit.Void, name: NO_SYM };
        for k in 0..self.ast.blockLen(b) {
            st: Stmt = self.ast.stmtAt(b, k);
            if (st.kind == StmtKind.Return) {
                v: NodeId = self.ast.returns.get(st.at).value;
                if (v == NO_NODE) { return none; }
                e: Expr = self.ast.expr(v);
                return TypeRef { base: e.kind, name: e.structName };
            }
            inner: TypeRef = self.nestedReturnType(st);
            if (inner.base != Lit.Void) { return inner; }
        }
        return none;
    }

    // The blocks a statement can hold, searched in turn.
    nestedReturnType &self st:Stmt -> TypeRef {
        none: TypeRef = TypeRef { base: Lit.Void, name: NO_SYM };
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                n: IfNode = self.ast.ifs.get(at);
                r: TypeRef = self.firstReturnType(n.body);
                if (r.base != Lit.Void) { return r; }
                at = n.elseIf;
            }
            return none;
        }
        if (st.kind == StmtKind.While) { return self.firstReturnType(self.ast.whiles.get(st.at).body); }
        if (st.kind == StmtKind.Recover) {
            w: WhileNode = self.ast.whiles.get(st.at);
            r: TypeRef = self.firstReturnType(w.body);
            if (r.base != Lit.Void) { return r; }
            return self.firstReturnType(w.step);
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
            return self.firstReturnType(self.ast.blockStmts.get(st.at).body);
        }
        if (st.kind == StmtKind.With) { return self.firstReturnType(self.ast.withs.get(st.at).body); }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = self.ast.matches.get(st.at);
            for k in 0..m.armCount {
                r: TypeRef = self.firstReturnType(self.ast.arms.get(m.firstArm + k).body);
                if (r.base != Lit.Void) { return r; }
            }
        }
        return none;
    }

    // `|a: T, b: U|`, or `||` for none (the lexer reads the empty pair as one token).
    parseClosureParams &self -> Vec<long> {
        out: Vec<long>;
        if (self.eat(Tok.LogicalOr)) { return out; }
        self.expect(Tok.Pipe);
        // Comma-separated, unlike a function's, because a bar has to end the list and a bare
        // sequence of names would not say where.
        more: bool = true;
        while (more && self.check(Tok.Id)) {
            out.extend(self.parseParamList(false));
            more = self.eat(Tok.Comma);
        }
        self.expect(Tok.Pipe);
        return out;
    }

    // The name a closure's value has. With no type parameters in scope that is the capture struct
    // itself. Inside a generic function it is not: what the closure captures is typed by that
    // function's parameters, so the struct is a template and the value is its instance at those
    // same parameters, a pattern instance, which monomorphization rebuilds and requests once an
    // enclosing stamp binds them, exactly as it does for `Mutex<W>` written in `BufWriter<W>`.
    closurePattern &self base:Sym -> Sym {
        if (self.typeVars.len() == 0) { return base; }
        s: String;
        s.pushStr(nameOf(base));
        for k in 0..self.typeVars.len() {
            s.push('_');
            s.pushStr(nameOf(self.typeVars.get(k)));
        }
        return internString(s);
    }

    // The capture struct: one field per captured variable, laid out like any other, or, inside a
    // generic function, a template over that function's parameters and a request for the instance
    // at them. A concrete registration cannot serve there: it would be emitted once with `T`
    // unsubstituted, and the closure's own `call` would keep calling the parameter's name.
    declareClosureStruct &self base:Sym caps:Vec<Capture> -> void {
        fields: Vec<FieldDef>;
        gfields: Vec<GField>;
        cursor: long = 0;
        for k in 0..caps.len() {
            c: Capture = caps.get(k);
            f: TypeRef = self.captureField(c.kind, c.structName, c.byPtr);
            fk: Lit = f.base;
            fs: Sym = f.name;
            p: Placed = placeField(cursor, FieldDef { name: c.name, kind: fk, structName: fs,
                                                      offset: 0, isArray: false, count: 0 });
            fields.push(p.field);
            gfields.push(GField { name: c.name, kind: TypeRef { base: fk, name: fs },
                                  isArray: false, count: 0 });
            cursor = p.next;
        }
        if (self.typeVars.len() == 0) {
            regAddStruct(base, fields, alignUp(cursor, 8), false);
            regMarkClosure(base);
        } else {
            // The layout computed above is discarded: a field whose type is still a parameter has
            // no size yet, and the stamp lays each instance out from what its arguments turned
            // out to be.
            params: Vec<Sym>;
            args: Vec<TypeRef>;
            for j in 0..self.typeVars.len() {
                params.push(self.typeVars.get(j));
                args.push(TypeRef { base: Lit.TypeVar, name: self.typeVars.get(j) });
            }
            // Over the parameters in scope as they are (a length is still one), not over whatever
            // the enclosing header's own reading of them left behind.
            saved: Vec<GParamInfo>;
            saved.extend(self.tplParams);
            self.tplParams = self.paramInfosOf(params);
            self.recordTemplate(base, params, gfields, false);
            self.tplParams = saved;
            regMarkClosure(base);
            regRequest(base, self.closurePattern(base), args, self.plainBody);
        }
        self.ast.structDecls.push(base);
        self.pending.push(self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1));
    }

    // `FnN`, made on demand rather than declared. There is one per arity because a trait cannot be
    // variadic in its type parameters, and writing them out in `core` capped the arities at however
    // many someone had typed: `parseFnSugar` then carried its own copy of that number as well.
    //
    // Built to the shape `parseTraitDecl` leaves behind, field for field, so nothing downstream can
    // tell a synthesized trait from a written one: `paramCount` counts the arguments AND the result,
    // which is what `stampTrait` matches its argument list against. The parameters are `T0..Tn-1`
    // and the result `R` because the names only have to be consistent with each other; stamping
    // substitutes by them, and no user type can collide with a name this never resolves.
    fnTraitFor &self n:long -> Sym {
        // A trait's name is flat, so the spelling IS the name and there is nothing to resolve.
        q: Sym = internString(format("Fn{}", n));
        if (gReg.findTraitSym(q) >= 0) { return q; }

        params: Vec<TypeRef>;
        ps: Vec<long>;
        for k in 0..n {
            tv: Sym = internString(format("T{}", k));
            params.push(TypeRef { base: Lit.TypeVar, name: tv });
            self.ast.decls.push(VarDeclNode { name: internString(format("a{}", k)),
                                              kind: Lit.TypeVar, structName: tv,
                                              isArray: false, count: 0, conv: Conv.None,
                                              isVariadic: false, elemKind: Lit.Void,
                                              elemStruct: NO_SYM, init: NO_NODE });
            ps.push(self.ast.decls.len() - 1);
        }
        rv: Sym = intern("R");
        params.push(TypeRef { base: Lit.TypeVar, name: rv });

        sigs: Vec<TraitMethodSig>;
        sigs.push(TraitMethodSig { name: intern("call"), returnKind: Lit.TypeVar, returnName: rv,
                                   firstParam: self.ast.addParams(ps), paramCount: ps.len(),
                                   isStatic: false, lentSelf: true });
        regDeclareTrait(q, sigs, params, &self.ast);
        self.ast.structDecls.push(q);
        self.pending.push(self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1));
        return q;
    }

    // The body as a method: `__cl` first, then the closure's own parameters. Registered as the
    // struct's implementation of `FnN`, which is what a bound or a trait object dispatches to.
    declareClosureCall &self base:Sym params:Vec<long> ret:TypeRef explicit:bool body:long -> void {
        self.ast.decls.push(VarDeclNode { name: intern("__cl"), kind: Lit.Ref, structName: base,
                                          isArray: false, count: 0, conv: Conv.Inout,
                                          isVariadic: false, elemKind: Lit.Void,
                                          elemStruct: NO_SYM, init: NO_NODE });
        all: Vec<long>;
        all.push(self.ast.decls.len() - 1);
        all.extend(params);

        // Registered against the bare `FnN`, not an instantiation of it: a bound asks only for
        // the name, and naming the instance here would fix the method's spelling to a return type
        // the body has only been guessed at. `aimTraitObj` adds the precise one where a trait
        // object needs a table with an exact name.
        tbase: Sym = self.fnTraitFor(params.len());
        tr: TraitRef = TraitRef { name: tbase, firstArg: 0, argCount: 0 };

        name: Sym = methodName(base, intern("call"));
        first: long = self.ast.addParams(all);
        // Trusted exactly where its text is: inside `unsafe`, the body is one trusted region, and
        // elsewhere it is safe code. The capture reads this desugaring wrote are not the author's
        // raw-pointer reads, and the checker knows them by shape (`Checker.captureRead`).
        self.ast.fns.push(FnNode { name: name, returnKind: ret.base, returnStruct: ret.name,
                                   visibility: Vis.Pub, file: self.lx.currentFile,
                                   pkg: self.lx.currentPackage, isUnsafe: self.unsafeDepth > 0,
                                   // A template alongside its struct, so the stamp clones it per
                                   // instance: `$closureN_call` is what `cloneMethods` finds by
                                   // the struct's own prefix.
                                   isTemplate: self.typeVars.len() > 0,
                                   firstBound: 0, boundCount: 0,
                                   firstArg: first, argCount: all.len(), body: body,
                                   inferReturn: !explicit });
        self.pending.push(self.ast.addStmt(StmtKind.FunctionDef, self.ast.fns.len() - 1));
        fns: Vec<Sym>;
        fns.push(name);
        regAddImpl(base, tr, fns, false);
    }

    // The value: the struct, built from each capture's expression in the scope it was met in.
    closureLiteral &self base:Sym caps:Vec<Capture> -> NodeId {
        inits: Vec<InitNode>;
        for k in 0..caps.len() {
            c: Capture = caps.get(k);
            inits.push(InitNode { name: c.name, value: c.value });
        }
        first: long = self.ast.addInits(inits);
        self.ast.lits.push(LitNode { typeName: self.closurePattern(base), firstInit: first,
                                     initCount: inits.len(), rest: NO_NODE });
        return self.ast.leafOf(Op.StructLit, Payload.Lit(self.ast.lits.len() - 1),
                               Lit.Struct, self.closurePattern(base));
    }

    // ─── names ───────────────────────────────────────────────────────────────

    currentModule &self -> str { return stemOf(nameOf(self.lx.currentFile)); }

    // The one name the runtime looks up bare, so it is never qualified: `main`, which `_start`
    // calls. (Startup and shutdown hooks are declared `@init`/`@fini`, never found by name.)
    isRuntimeHook &self n:str -> bool { return n == "main"; }

    // A bare name resolved against what this file can see, reported here when two reachable
    // modules declare it: the registry answers the question, the parser owns the line number.
    resolveHere &self bare:str -> Sym {
        b: BareName = gReg.resolveBareIn(self.currentModule(), bare);
        if (b.rival != NO_SYM) { self.err(ambiguousName(bare, b)); }
        return b.name;
    }

    // What already holds `bare` as a type name in this module, or "" if it is free. The list is
    // exactly what `parseTypeRef` searches, in the order it searches: built-in scalars, aliases,
    // structs, templates, enums, traits, because that search returns the first hit, so two
    // declarations under one name never both exist and the loser silently stops being reachable.
    // An `enum Foo` beside a `struct Foo` is not a choice anyone made; it is a declaration that
    // quietly did nothing.
    typeNameOwner &self bare:str -> str {
        if (namesScalar(bare)) { return "a built-in type"; }
        q: str = nameOf(self.qualify(bare));
        if (gReg.findAlias(q) >= 0) { return "a type alias"; }
        if (gReg.hasStruct(q)) { return "a struct"; }
        at: long = gReg.findTemplate(q);
        if (at >= 0) {
            if (gReg.templateDef(at).isEnum) { return "a generic enum"; }
            return "a generic struct";
        }
        if (gReg.findEnum(q) >= 0) { return "an enum"; }
        // A `pub` trait's name is flat, so it is asked for as written; a file's own, qualified.
        if (gReg.findTrait(bare) >= 0 || gReg.findTrait(q) >= 0) { return "a trait"; }
        return "";
    }

    requireTypeNameFree &self bare:str -> void {
        owner: str = self.typeNameOwner(bare);
        if (owner.len > 0) {
            self.err(format("the type name `{}` is already taken by {}", bare, owner));
        }
    }
    // The same, asking only about this module's own names: what a file-owned trait claims.
    requireOwnTypeNameFree &self bare:str -> void {
        owner: str = "";
        q: str = nameOf(self.qualify(bare));
        if (namesScalar(bare)) { owner = "a built-in type"; }
        else if (gReg.findAlias(q) >= 0) { owner = "a type alias"; }
        else if (gReg.hasStruct(q)) { owner = "a struct"; }
        else if (gReg.findTemplate(q) >= 0) { owner = "a generic type"; }
        else if (gReg.findEnum(q) >= 0) { owner = "an enum"; }
        if (owner.len > 0) {
            self.err(format("the type name `{}` is already taken by {}", bare, owner));
        }
    }

    // A top-level name belongs to the module that declared it, so that two modules may use the
    // same one without colliding.
    qualify &self bare:str -> Sym {
        if (self.isRuntimeHook(bare)) { return intern(bare); }
        s: String;
        s.pushStr(self.currentModule());
        s.pushStr("::");
        s.pushStr(bare);
        out: Sym = NO_SYM;
        out = internString(s);
        return out;
    }

    // ─── expressions ─────────────────────────────────────────────────────────

    // Splice `op` into the tree at the place its precedence says it belongs. `<=` rather than `<`
    // makes equal precedence left-associative, so `10 - 5 + 2` is `(10 - 5) + 2`. A parenthesised
    // subtree is opaque: nothing is ever inserted inside it.
    insertOp &self head:NodeId op:Op value:NodeId -> NodeId {
        if (head == NO_NODE) { return value; }
        h: Expr = self.ast.expr(head);
        if (h.isParen || precedenceOf(op) <= precedenceOf(h.op)) {
            return self.ast.binary(op, head, value, higherPrecedence(h.kind, self.ast.expr(value).kind));
        }
        if (h.right == NO_NODE) { h.right = value; }
        else { h.right = self.insertOp(h.right, op, value); }
        self.ast.setExpr(head, h);
        return head;
    }

    // The operator the current token starts, or Op.Literal for "not an operator". Consumes
    // nothing.
    peekBinOp &self -> Op {
        k: Tok = self.cur.kind;
        if (k == Tok.Plus)  { return Op.Addition; }
        if (k == Tok.Dash)  { return Op.Subtraction; }
        if (k == Tok.Star)  { return Op.Multiplication; }
        if (k == Tok.Slash) { return Op.Division; }
        if (k == Tok.Percent) { return Op.Modulus; }
        if (k == Tok.LessThan) { return Op.LessThan; }
        if (k == Tok.GreaterThan) { return Op.GreaterThan; }
        if (k == Tok.IsLessOrEqual) { return Op.IsLessOrEqual; }
        if (k == Tok.IsGreaterOrEqual) { return Op.IsGreaterOrEqual; }
        if (k == Tok.IsEqual) { return Op.IsEqual; }
        if (k == Tok.IsNotEqual) { return Op.IsNotEqual; }
        if (k == Tok.Ampersand) { return Op.BitwiseAnd; }
        if (k == Tok.Pipe) { return Op.BitwiseOr; }
        if (k == Tok.Caret) { return Op.BitwiseXor; }
        if (k == Tok.ShiftLeft) { return Op.ShiftLeft; }
        if (k == Tok.ShiftRight) { return Op.ShiftRight; }
        if (k == Tok.LogicalAnd) { return Op.LogicalAnd; }
        if (k == Tok.LogicalOr) { return Op.LogicalOr; }
        return Op.Literal;                    // "no operator here"
    }

    // A whole expression, up to but not including the terminator.
    // A full expression is its own context: `*(a as *long)` casts inside the parentheses, and the
    // withholding a prefix operator does applies only to the operand chain it is reading, not to
    // anything bracketed within it.
    parseExpr &self -> NodeId {
        was: long = self.noCast;
        self.noCast = 0;
        v: NodeId = self.parseExprHere();
        self.noCast = was;
        return v;
    }

    parseExprHere &self -> NodeId { return self.continueExpr(self.parseAtom()); }

    // The rest of an expression whose first operand is read: each operator and the operand after
    // it, put where precedence says. A statement that begins with a name reads the name's chain
    // first and only then finds an operator after it.
    continueExpr &self first:NodeId -> NodeId {
        head: NodeId = first;
        going: bool = true;
        while (going) {
            op: Op = self.peekBinOp();
            if (op == Op.Literal) { going = false; }
            else {
                self.advance();
                head = self.insertOp(head, op, self.parseAtom());
            }
        }
        return head;
    }

    // A leaf, with any prefix operator and any postfix chain attached.
    parseAtom &self -> NodeId {
        // `|x| …` and `||`: a closure literal.
        if (self.check(Tok.Pipe) || self.check(Tok.LogicalOr)) { return self.parseClosure(); }
        // Prefix operators. `-x` is `0 - x` so that nothing downstream needs an arm for it, and a
        // negated literal folds into the literal.
        if (self.check(Tok.Dash)) {
            self.advance();
            v: NodeId = self.parseAtom();
            e: Expr = self.ast.expr(v);
            p: Payload = e.payload;
            match p {
                Num(n) {
                    if (e.op == Op.Literal) {
                        // A literal past `long`'s maximum is a u64's: negated, only 2^63 has a
                        // value, `long`'s minimum.
                        if (e.kind == Lit.U64) {
                            if (n != 0 - n) {
                                self.err(format("literal `-{}` out of range for `long`\nnote: the smallest `long` is -9223372036854775808", n as u64));
                            }
                            return self.numberLit(n, Lit.Long);
                        }
                        return self.numberLit(0 - n, e.kind);
                    }
                }
                // A float literal's spelling takes the sign: `-1.5` is one literal, and `-0.0` is
                // negative zero, which `0 - 0.0` is not.
                Text(t) {
                    if (e.op == Op.Literal) {
                        s: str = nameOf(t);
                        neg: Sym = NO_SYM;
                        if (s.len > 0 && charAt(s, 0) == '-') { neg = intern(strSlice(s, 1, s.len - 1)); }
                        else { neg = internString(format("-{}", s)); }
                        return self.ast.leaf(Op.Literal, Payload.Text(neg), e.kind);
                    }
                }
                _ { }
            }
            // The zero is marked (`isParen`, which a leaf has no other use for): over a float it
            // is not a subtraction from zero but a negation, which flips the sign of a zero and of
            // a NaN as well (`checkBinary`, `lowerExpr`).
            zero: NodeId = self.numberLit(0, e.kind);
            ze: Expr = self.ast.expr(zero);
            ze.isParen = true;
            self.ast.setExpr(zero, ze);
            return self.ast.binary(Op.Subtraction, zero, v, e.kind);
        }
        if (self.check(Tok.Exclamation)) {
            self.advance();
            return self.ast.unary(Op.LogicalNot, self.parseAtom(), Lit.Bool);
        }
        if (self.check(Tok.Tilde)) {
            self.advance();
            v: NodeId = self.parseAtom();
            return self.ast.unary(Op.BitwiseNot, v, self.ast.expr(v).kind);
        }
        // `*p` and `&x`. The operand is a postfix chain: `&self.flag`, `*a[i]`, but not a
        // cast: `&x as *int` is `(&x) as *int`, the address cast to a pointer, and letting the
        // operand's postfix take the `as` first would build `&(x as *int)` instead. So `as` is
        // withheld while the operand is read and applied to the finished node.
        if (self.check(Tok.Star)) {
            self.advance();
            v: NodeId = self.parseOperand();
            // What `*p` yields is the pointee, which only the checker can read out of the
            // pointer's companion name. Until then the node carries the operand's own type
            // rather than a guess at `long`, which would be wrong for every pointer to anything
            // else.
            return self.parsePostfix(self.ast.unary(Op.Deref, v, self.ast.expr(v).kind));
        }
        if (self.check(Tok.Ampersand)) {
            self.advance();
            return self.parsePostfix(self.ast.unary(Op.AddressOf, self.parseOperand(), Lit.Long));
        }

        if (self.check(Tok.LeftParen)) {
            self.advance();
            inner: NodeId = self.parseExpr();
            if (self.check(Tok.Comma)) { return self.parsePostfix(self.parseTupleLit(inner)); }
            self.expect(Tok.RightParen);
            e: Expr = self.ast.expr(inner);
            e.isParen = true;
            self.ast.setExpr(inner, e);
            return self.parsePostfix(inner);
        }

        if (self.check(Tok.IntLiteral))  { return self.parsePostfix(self.numberLit(self.advance().num, Lit.Int)); }
        if (self.check(Tok.LongLiteral)) { return self.parsePostfix(self.numberLit(self.advance().num, Lit.Long)); }
        if (self.check(Tok.U64Literal))  { return self.parsePostfix(self.numberLit(self.advance().num, Lit.U64)); }
        if (self.check(Tok.CharLiteral)) { return self.parsePostfix(self.numberLit(self.advance().num, Lit.Char)); }
        // A float literal keeps its spelling: whether it is an `f64` or an `f32` is settled where it
        // is used, and each is the decimal rounded once, to that width (`support::fp`).
        if (self.check(Tok.FloatLiteral)) {
            t: Token = self.advance();
            return self.parsePostfix(self.ast.leaf(Op.Literal, Payload.Text(t.text), Lit.Double));
        }
        if (self.check(Tok.StringLiteral)) {
            t: Token = self.advance();
            return self.parsePostfix(self.ast.leaf(Op.StringLit,
                                                   Payload.Text(unquoted(t.text)), Lit.Str));
        }
        if (self.check(Tok.Literal)) {                   // `true` / `false`
            t: Token = self.advance();
            v: long = 0;
            if (eqNoCase(nameOf(t.text), "true")) { v = 1; }
            return self.parsePostfix(self.numberLit(v, Lit.Bool));
        }

        // `@x` inside a quote is a splice: the Node that `x` holds goes here. Outside a quote `@`
        // still opens a macro statement. `@x` is the variable alone and `@(e)` the parenthesized
        // expression, so whatever follows (`.f`, `.m(...)`, `[i]`) is quoted, and applies to the
        // spliced tree.
        if (self.quoteDepth > 0 && self.check(Tok.AtSign)) {
            self.advance();
            held: NodeId = self.parseSpliceHeld();
            q: Quoter = self.quoter();
            return self.parsePostfix(self.ast.leafOf(Op.Splice, Payload.Sub(held), Lit.Struct, q.node));
        }
        // `quote { expr }` -> a Node value that is that expression. See quoteTree.
        if (self.word("quote") && self.peekNext().kind == Tok.LeftCurly) {
            self.advance();
            return self.parseQuote();
        }
        if (self.word("sizeof")) {
            self.advance();
            self.expect(Tok.LeftParen);
            t: TypeRef = self.parseTypeRef();
            self.expect(Tok.RightParen);
            return self.parsePostfix(self.ast.sizeofNode(t.base, t.name));
        }
        // `nameof(E, v)` -> the name of the variant `v` holds, as a str. The enum has to be named:
        // a backed enum's value is just its backing integer at runtime and carries no type. That
        // is also what lets the answer be built from the declaration rather than kept by hand:
        // 43 of this compiler's own 47 token names were exactly that table. The checker rewrites
        // it into a call to a derived `E_nameof`, so nothing after it knows the builtin exists,
        // exactly as `sizeof` becomes a literal.
        if (self.word("nameof")) {
            self.advance();
            self.expect(Tok.LeftParen);
            // Read directly rather than through `parseTypeRef`, which resolves a backed enum to
            // its backing int and loses which enum it was.
            bare: Token = self.expect(Tok.Id);
            en: Sym = self.resolveHere(nameOf(bare.text));
            if (!gReg.isEnumTypeSym(en)) {
                self.err(format("`{}` is not an enum\nnote: `nameof(E, v)` names the variant of enum `E` that `v` holds",
                                nameOf(bare.text)));
            }
            self.expect(Tok.Comma);
            val: NodeId = self.parseExpr();
            self.expect(Tok.RightParen);
            return self.parsePostfix(self.ast.leafOf(Op.Nameof, Payload.Sub(val), Lit.Str, en));
        }
        if (self.check(Tok.Id)) { return self.parseNamed(); }
        // `[a, b, c]`: an array's elements, where an array is declared (`xs: [long; 3] = [...]`).
        if (self.check(Tok.LeftSquare)) {
            self.advance();
            inits: Vec<InitNode>;
            while (!self.check(Tok.RightSquare) && !self.check(Tok.FileEnd)) {
                inits.push(InitNode { name: NO_SYM, value: self.parseExpr() });
                if (!self.eat(Tok.Comma)) { break; }
            }
            self.expect(Tok.RightSquare);
            at: long = self.ast.addInits(inits);
            self.ast.lits.push(LitNode { typeName: NO_SYM, firstInit: at, initCount: inits.len(),
                                         rest: NO_NODE });
            return self.ast.leaf(Op.ArrayLit, Payload.Lit(self.ast.lits.len() - 1), Lit.Void);
        }

        self.err(format("expected an expression, found {}", describeTok(self.cur)));
        return NO_NODE;
    }

    // A reference to an already-declared local.
    nameRef &self n:Sym k:Lit sname:Sym -> NodeId {
        v: NodeId = self.ast.leaf(Op.Lvalue, Payload.Name(n), k);
        e: Expr = self.ast.expr(v);
        self.ast.setExpr(v, Expr { op: e.op, left: e.left, right: e.right, kind: k,
                                   structName: sname, isParen: false, payload: e.payload });
        return v;
    }

    numberLit &self v:long k:Lit -> NodeId {
        return self.ast.leaf(Op.Literal, Payload.Num(v), k);
    }

    // An identifier: a variable, a call, or a cast's `as` is handled by the postfix chain.
    parseNamed &self -> NodeId {
        name: Token = self.advance();
        return self.parseNamedFrom(name);
    }

    // The same, for a caller that has already taken the identifier off the stream: a statement
    // beginning with a name looks like a declaration or a function definition until several
    // tokens later, so `parseFromName` consumes it before it can know. It is one function rather
    // than two because a statement's leading name means everything an expression's does,
    // including being a closure capture, and a second copy would have to keep up with all of it.
    parseNamedFrom &self name:Token -> NodeId {
        // `T.max()` inside a blanket implementation: the scalar this reading is for.
        if (self.blanketVar != NO_SYM && name.text == self.blanketVar && self.bindingOf(name.text).renamed == NO_SYM) {
            name = tokenText(Tok.Id, self.blanketAs);
        }

        // `mod::name`, the module is spelled out. Rewritten to the qualified symbol, after which
        // it behaves exactly like a bare name that resolved to the same place.
        if (self.check(Tok.ColonColon)) {
            q: Sym = self.qualifiedFrom(name);
            name = tokenText(Tok.Id, q);
        }

        // A name a local declares is that local, and nothing else. Asked once, before any of the
        // branches that read a name as a type: `s.len` where `s` is a variable must not become a
        // member of a type that happens to share its name, and `a < b` must not become an
        // instantiation.
        isLocal: bool = self.bindingOf(name.text).renamed != NO_SYM;

        // `Name { ... }`: a struct literal, but only for a name that is a struct: an ordinary
        // variable followed by a block is a condition, not a construction.
        if (!isLocal && self.check(Tok.LessThan)) {
            base: Sym = self.resolveHere(nameOf(name.text));
            if (gReg.isGenericSym(base)) {
                inst: TypeRef = self.parseGenericArgs(base);
                return self.parsePostfix(self.parseStructLit(inst.name));
            }
        }
        if (!isLocal && self.check(Tok.LeftCurly)) {
            q: Sym = self.resolveHere(nameOf(name.text));
            // A template counts: inside `methods Vec<T>` the literal `Vec { ... }` names the
            // instance being stamped out, which does not exist as a struct yet.
            if (gReg.hasStructSym(q) || gReg.isGenericSym(q)) {
                return self.parsePostfix(self.parseStructLit(q));
            }
        }

        // `Option.Some(v)` / `Option.None`: constructing a sum type's variant. Desugared here
        // into the struct literal the layout actually is: the tag, then that variant's payload
        // fields. Nothing downstream then has to know a variant constructor exists.
        if (!isLocal && self.check(Tok.Dot)) {
            owner: Sym = self.resolveHere(nameOf(name.text));
            if (gReg.isSumType(nameOf(owner)) || self.isGenericSum(nameOf(owner))) {
                self.advance();                           // '.'
                v: Token = self.expect(Tok.Id);
                // `SA.parse(s)`: not a variant but a static method of the sum type, called on the
                // type as on any other. A variant and a method of one name are refused where the
                // method is declared, so a name that is a variant is always the variant.
                if (self.check(Tok.LeftParen) && !self.sumHasVariant(owner, v.text)) {
                    self.advance();
                    sargs: Vec<NodeId> = self.parseArgs();
                    self.ast.calls.push(CallNode { name: v.text, receiver: self.nameRef(owner, Lit.Struct, owner),
                                                   firstArg: self.ast.addArgs(sargs), argCount: sargs.len(),
                                                   slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
                    return self.parsePostfix(self.ast.leaf(Op.MethodCall, Payload.Call(self.ast.calls.len() - 1), Lit.Void));
                }
                return self.parsePostfix(self.parseVariant(owner, v.text));
            }
            // An enum with no payloads is a set of named integers: `BoxTag.Str` is its value and
            // nothing downstream ever sees a variant. Read as a field access it would become a
            // load from a global nobody declared, and every comparison against one would be false.
            if (gReg.isEnumTypeSym(owner)) {
                self.advance();
                v: Token = self.expect(Tok.Id);
                // `Color.decode(inp)`: not a variant but a static method of the enum (one a
                // trait gives it, `methods Color for Decode`), called on the type.
                if (self.check(Tok.LeftParen)
                    && gReg.findVariant(gReg.enumDef(gReg.findEnumSym(owner)), nameOf(v.text)) < 0) {
                    self.advance();
                    sargs: Vec<NodeId> = self.parseArgs();
                    self.ast.calls.push(CallNode { name: v.text, receiver: self.nameRef(owner, Lit.Struct, owner),
                                                   firstArg: self.ast.addArgs(sargs), argCount: sargs.len(),
                                                   slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
                    return self.parsePostfix(self.ast.leaf(Op.MethodCall, Payload.Call(self.ast.calls.len() - 1), Lit.Void));
                }
                return self.parsePostfix(self.enumConst(owner, v.text));
            }
        }

        // A name the enclosing scope declared, met inside a closure body, is captured, and it is
        // rewritten here, where it is resolved, rather than by a second walk afterwards.
        cap: NodeId = self.captureOf(name.text);
        if (cap != NO_NODE) {
            // A captured value that is called is another closure: `pred(x)` inside one is
            // `<the captured pred>.call(x)`.
            if (!self.check(Tok.LeftParen)) { return self.parsePostfix(cap); }
            self.advance();
            cargs: Vec<NodeId> = self.parseArgs();
            self.ast.calls.push(CallNode { name: intern("call"), receiver: cap,
                                           firstArg: self.ast.addArgs(cargs),
                                           argCount: cargs.len(), slot: NO_SLOT,
                                           callee: NO_NODE, sigKey: NO_SYM });
            return self.parsePostfix(self.ast.leaf(Op.FunctionCall,
                                                   Payload.Call(self.ast.calls.len() - 1),
                                                   Lit.Void));
        }

        // `name!(args)` is a macro call: the compiler runs `name` while checking and puts what it
        // returned here. The arguments are read as ordinary expressions, and the macro's
        // signature decides, once the checker has it, which of them it takes as a tree.
        // `name![ ... ]` is the raw form: the macro gets the source text between the brackets as
        // a `str` and reads it however it likes, using `parseExpr` to read a piece of it as code.
        // In short, with parentheses the compiler parses the arguments, and with brackets the
        // macro does.
        if (self.check(Tok.Exclamation) && self.peekNext().kind == Tok.LeftSquare) {
            self.advance();
            self.advance();
            text: Sym = self.rawUntilClose();
            rargs: Vec<NodeId>;
            rargs.push(self.ast.leaf(Op.StringLit, Payload.Text(text), Lit.Str));
            rfirst: long = self.ast.addArgs(rargs);
            self.ast.calls.push(CallNode { name: name.text, receiver: NO_NODE,
                                           firstArg: rfirst, argCount: 1, slot: NO_SLOT,
                                           callee: NO_NODE, sigKey: NO_SYM });
            return self.parsePostfix(self.ast.leaf(Op.MacroCall, Payload.Call(self.ast.calls.len() - 1), Lit.Int));
        }
        if (self.check(Tok.Exclamation) && self.peekNext().kind == Tok.LeftParen) {
            self.advance();
            self.advance();
            margs: Vec<NodeId> = self.parseArgs();
            mfirst: long = self.ast.addArgs(margs);
            self.ast.calls.push(CallNode { name: name.text, receiver: NO_NODE,
                                           firstArg: mfirst, argCount: margs.len(), slot: NO_SLOT,
                                           callee: NO_NODE, sigKey: NO_SYM });
            return self.parsePostfix(self.ast.leaf(Op.MacroCall, Payload.Call(self.ast.calls.len() - 1), Lit.Int));
        }
        if (self.check(Tok.LeftParen)) {                 // a call
            self.advance();
            args: Vec<NodeId> = self.parseArgs();
            first: long = self.ast.addArgs(args);
            self.ast.calls.push(CallNode { name: name.text, receiver: NO_NODE,
                                           firstArg: first, argCount: args.len() , slot: NO_SLOT,
                                           callee: NO_NODE, sigKey: NO_SYM });
            id: long = self.ast.calls.len() - 1;
            return self.parsePostfix(self.ast.leaf(Op.FunctionCall, Payload.Call(id),
                                                   self.calleeReturn(name.text)));
        }

        b: Binding = self.bindingOf(name.text);
        renamed: Sym = name.text;
        kind: Lit = Lit.Long;
        sname: Sym = NO_SYM;
        if (b.renamed != NO_SYM) { renamed = b.renamed; kind = b.kind; sname = b.structName; }

        v: NodeId = self.ast.leaf(Op.Lvalue, Payload.Name(renamed), kind);
        e: Expr = self.ast.expr(v);
        e.structName = sname;
        e.isParen = false;
        self.ast.setExpr(v, e);
        // An `inout` scalar parameter is read and written where the caller keeps it.
        if (b.renamed != NO_SYM && kind == Lit.Ref && isInoutScalarName(sname)) {
            st: TypeRef = inoutScalarOf(sname);
            v = self.ast.addExpr(Expr { op: Op.Deref, left: NO_NODE, right: NO_NODE, kind: st.base,
                                        structName: st.name, isParen: false, payload: Payload.Sub(v) });
        }
        return self.parsePostfix(v);
    }

    // Arguments up to the closing paren, which this consumes.
    parseArgs &self -> Vec<NodeId> {
        out: Vec<NodeId>;
        if (self.eat(Tok.RightParen)) { return out; }
        going: bool = true;
        while (going) {
            out.push(self.parseExpr());
            if (!self.eat(Tok.Comma)) { going = false; }
        }
        self.expect(Tok.RightParen);
        return out;
    }

    // A prefix operator's operand: everything a postfix chain gives, minus the cast.
    parseOperand &self -> NodeId {
        self.noCast = self.noCast + 1;
        v: NodeId = self.parseAtom();
        self.noCast = self.noCast - 1;
        return v;
    }

    // `.field`, `.method(...)`, `[index]`, `?` and `as Type`, chained for as long as they continue.
    parsePostfix &self v:NodeId -> NodeId {
        going: bool = true;
        while (going) {
            if (self.check(Tok.Question)) {
                self.advance();
                v = self.tryHoleFor(v);
                continue;
            }
            if (self.check(Tok.Dot)) {
                self.advance();
                // `.@(f.name)` inside a quote: the field or method is named by a `str` the macro
                // computes. Carried as a name the quoter recognizes (`splicedName`).
                name: Token = Token { kind: Tok.Id, text: NO_SYM, num: 0 };
                if (self.quoteDepth > 0 && self.check(Tok.AtSign)) {
                    self.advance();
                    name = Token { kind: Tok.Id, text: splicedName(self.parseSpliceHeld()), num: 0 };
                } else if (self.check(Tok.IntLiteral)) {
                    // `t.0`: a tuple's element by position, the field the registry placed it in.
                    // The lexer has no fractional literals, so `t.0.1` is two of these.
                    k: Token = self.advance();
                    name = Token { kind: Tok.Id, text: tupleFieldName(k.num), num: 0 };
                } else {
                    name = self.expect(Tok.Id);
                }
                if (self.check(Tok.LeftParen)) {
                    self.advance();
                    args: Vec<NodeId> = self.parseArgs();
                    first: long = self.ast.addArgs(args);
                    self.ast.calls.push(CallNode { name: name.text, receiver: v,
                                                   firstArg: first, argCount: args.len() , slot: NO_SLOT,
                                                   callee: NO_NODE, sigKey: NO_SYM });
                    id: long = self.ast.calls.len() - 1;
                    v = self.ast.leaf(Op.MethodCall, Payload.Call(id), Lit.Void);
                } else {
                    self.ast.fields.push(FieldNode { base: v, name: name.text });
                    id: long = self.ast.fields.len() - 1;
                    v = self.ast.leaf(Op.FieldAccess, Payload.Field(id), Lit.Void);
                }
            } else if (self.check(Tok.LeftSquare)) {
                self.advance();
                // Taken here, at the bracket, and not after the subscript: the index may be a
                // call spanning lines, and what a failing check should name is where the
                // indexing was written.
                at: Sym = self.sourceHere();
                ix: IndexParts = self.parseIndexOrRange();
                self.expect(Tok.RightSquare);
                self.ast.indexes.push(IndexNode { name: NO_SYM, base: v, index: ix.index,
                                                  whole: ix.whole, rawPointerBase: false,
                                                  sliceStart: ix.lo, sliceEnd: ix.hi, at: at });
                id: long = self.ast.indexes.len() - 1;
                // `int` is the placeholder an index carries until the checker reads the element
                // type out of the base. It is the placeholder the earlier compiler left, so an
                // assignment over one is typed the same way it was there.
                v = self.ast.leaf(Op.ArrayIndex, Payload.Index(id), Lit.Int);
            } else if (self.noCast == 0 && self.word("as")) {
                self.advance();
                t: TypeRef = self.parseTypeRef();
                cast: NodeId = self.ast.unary(Op.Cast, v, t.base);
                e: Expr = self.ast.expr(cast);
                self.ast.setExpr(cast, Expr { op: e.op, left: e.left, right: e.right, kind: t.base,
                                              structName: t.name, isParen: false,
                                              payload: e.payload });
                v = cast;
            } else {
                going = false;
            }
        }
        return v;
    }

    // What is between the brackets: one element, or a range. Entry: the '[' is consumed; the
    // ']' is the caller's. `..` is a terminator everywhere an expression is parsed, so a lower
    // bound stops there without needing lookahead.
    parseIndexOrRange &self -> IndexParts {
        if (self.eat(Tok.DotDot)) {                       // `[..]`, `[..hi]`
            hi: NodeId = NO_NODE;
            if (!self.check(Tok.RightSquare)) { hi = self.parseExpr(); }
            return IndexParts { index: NO_NODE, lo: NO_NODE, hi: hi, whole: true };
        }
        first: NodeId = self.parseExpr();
        if (self.eat(Tok.DotDot)) {                       // `[lo..]`, `[lo..hi]`
            hi: NodeId = NO_NODE;
            if (!self.check(Tok.RightSquare)) { hi = self.parseExpr(); }
            return IndexParts { index: NO_NODE, lo: first, hi: hi, whole: true };
        }
        return IndexParts { index: first, lo: NO_NODE, hi: NO_NODE, whole: false };
    }

    // ─── types ───────────────────────────────────────────────────────────────

    // A type as written: a scalar name, `*T`, `[T]`, or a named aggregate.
    parseTypeRef &self -> TypeRef {
        // A template argument may be a length rather than a type (`Buf<64>`), but only the
        // argument itself: nothing nested inside a type (`*T`, `[T]`, `fn(T)`) may be one.
        allowLen: bool = self.lenArgOk;
        self.lenArgOk = false;
        if (allowLen && (self.check(Tok.IntLiteral) || self.check(Tok.LongLiteral) || self.check(Tok.Dash))) {
            return lengthArg(self.parseAngleLength());
        }
        // `@(t.name)` where a quote reads a type: the macro computes its spelling, a `str`. It
        // has to stand alone, because `&@(x)` would have to build a spelling at the macro's run
        // time. A borrow of one is written `inout p:@(x)`, or spelled in full by the macro.
        if (self.quoteDepth > 0 && self.check(Tok.AtSign)) {
            self.advance();
            if (self.inPointee > 0) { self.err(stringOf("a spliced type cannot be part of another type\nhelp: build the whole spelling in the macro")); }
            return TypeRef { base: Lit.Struct, name: splicedName(self.parseSpliceHeld()) };
        }
        // `(A, B)`: a structural aggregate. Its elements are what it is, so they are registered
        // here under a name derived from them: the type has fields and a size from this point on,
        // and a `(long, long)` return is a 16-byte value rather than a word with the second half
        // missing. It is a struct from here on (`Lit.Struct` under the tuple's name), so it owns,
        // moves, copies, is laid out and crosses a call exactly as a struct with those fields
        // would: an element may be anything a struct field may be. A borrow may not: a tuple is a
        // value, and a `&T` field would be a pointer into a frame with no rule to hold it there.
        if (self.check(Tok.LeftParen)) {
            self.advance();
            elems: Vec<TypeRef>;
            while (!self.check(Tok.RightParen) && !self.check(Tok.FileEnd)) {
                t: TypeRef = self.parseTypeRef();
                if (t.base == Lit.Ref || t.base == Lit.Void || t.base == Lit.Len) {
                    self.err(format("`{}` cannot be a tuple element\nnote: a tuple element must be a value",
                                    typeMangleName(t.base, t.name)));
                }
                elems.push(t);
                self.eat(Tok.Comma);
            }
            self.expect(Tok.RightParen);
            if (elems.len() == 0) { self.err(stringOf("`()` is not a type\nnote: a tuple has at least one element")); }
            return namedTypeRef(Lit.Struct, regTuple(elems));
        }
        if (self.check(Tok.Star)) {                      // *T
            self.advance();
            self.inPointee = self.inPointee + 1;
            pointee: TypeRef = self.parseTypeRef();
            self.inPointee = self.inPointee - 1;
            return TypeRef { base: Lit.Ptr, name: intern(typeMangleName(pointee.base, pointee.name)) };
        }
        // `&T`: a borrow. A struct or a type parameter becomes a ref (a pointer to it); a
        // scalar's borrow is the scalar itself, since there is nothing to point at that is
        // cheaper than the value. `&&T` is not a thing: a borrow of a borrow is that borrow.
        if (self.check(Tok.Ampersand)) {
            self.advance();
            inner: TypeRef = self.parseTypeRef();
            if ((inner.base == Lit.Struct && !namedScalar(inner.base, inner.name)) || inner.base == Lit.TypeVar) {
                return TypeRef { base: Lit.Ref, name: inner.name };
            }
            if (inner.base == Lit.Ref) { return inner; }
            if (typeInfo(inner.base).aggregate) {
                self.err(format("`&` cannot borrow a {}\nnote: `&T` borrows a struct or a type parameter", typeName(inner.base)));
            }
            return inner;
        }
        if (self.check(Tok.LeftSquare)) {                // [T]
            self.advance();
            elem: TypeRef = self.parseTypeRef();
            self.expect(Tok.RightSquare);
            return TypeRef { base: Lit.Slice, name: intern(sliceElemName(elem.base, elem.name)) };
        }
        // `fn(A, B) -> R`. The whole signature is kept, not just the result: `fn(sink Res)->long`
        // hands its argument over where `fn(Res)->long` only lends it, and a pointer that cannot
        // say which is a pointer through which nobody can tell who releases the value. The
        // parameters and their conventions go into the signature table and the companion name is
        // the key they interned under.
        //
        // A signature mentioning a type parameter is registered too: `fn(T)->U` is a perfectly
        // good pattern to key by, and `Mono::concrete` rebuilds it under the bindings.
        if (self.word("fn")) {
            self.advance();
            self.expect(Tok.LeftParen);
            ps: Vec<FnParam>;
            while (!self.check(Tok.RightParen) && !self.check(Tok.FileEnd)) {
                // `fn(sink Res) -> long`: a fn type says how it takes a struct argument, the
                // same way the `Fn(...)` sugar does. It is part of the contract, not a type.
                conv: Conv = Conv.None;
                if (self.eatWord("sink")) { conv = Conv.Sink; }
                else if (self.eatWord("read")) { conv = Conv.Read; }
                p: TypeRef = self.parseTypeRef();
                ps.push(fnParamOf(p, conv));
                self.eat(Tok.Comma);
            }
            self.expect(Tok.RightParen);
            self.expect(Tok.Arrow);
            ret: TypeRef = self.parseTypeRef();
            return TypeRef { base: Lit.Fn, name: regFnSig(ps, ret) };
        }
        name: Token = self.expect(Tok.Id);
        // A blanket implementation's parameter is, in each reading, the scalar it is read for.
        if (self.blanketVar != NO_SYM && name.text == self.blanketVar) { return typeRefOf(scalarNamed(nameOf(self.blanketAs))); }
        spelling: str = nameOf(name.text);
        // A template parameter is a name that stands for a type, not one that names one. It has to
        // be recognised before anything qualifies it: `W` inside `BufWriter<W>` is not the struct
        // `write::W`, and mangling it as one stamps an instance of a type that does not exist.
        if (self.isTypeVar(name.text)) {
            self.typeVarUses = self.typeVarUses + 1;
            if (!allowLen && self.isLenVar(name.text)) {
                self.err(format("`{}` is a length parameter, not a type\nhelp: use it as an array's length (`[T; {}]`), as a value, or as a template's length argument",
                                spelling, spelling));
            }
            return TypeRef { base: Lit.TypeVar, name: name.text };
        }
        // `Fn(A, B) -> R`: sugar for `Fn2<A, B, R>`, the trait a callable of that shape
        // implements. Written wherever a type is: a bound, a parameter, a field.
        if (spelling == "Fn" && self.check(Tok.LeftParen)) { return self.parseFnSugar(); }
        if (namesScalar(spelling) && !self.check(Tok.ColonColon)) {
            return typeRefOf(scalarNamed(spelling));
        }
        written: str = spelling;
        if (self.check(Tok.ColonColon)) {
            written = keepString(format("{}::{}", spelling, nameOf(self.peekNext().text)));
        }
        q: Sym = self.qualifiedFrom(name);
        // `Buf<PATH_MAX>`: a template's length given as a constant global. A name that is a type
        // is a type, so a constant only stands here when nothing declares the name as one.
        if (allowLen && !self.check(Tok.LessThan) && !gReg.declares(nameOf(q))) {
            g: long = self.globalNamed(written, self.currentModule());
            if (g >= 0) { return lengthArg(self.constGlobalValue(g, written)); }
        }
        // A trait is checked before the generic-argument form: `Iter<long>` is one instantiation
        // of a trait, not an instance of a generic struct, and reading it as the latter asks for
        // a type nobody declared. Its arguments stamp a concrete trait, so everything downstream
        // deals only in those. One vtable per instance, one set of signatures.
        ti: long = gReg.findTraitSym(q);
        if (ti >= 0) {
            targs: Vec<TypeRef>;
            if (self.check(Tok.LessThan)) {
                self.advance();
                while (!self.atCloseAngle() && !self.check(Tok.FileEnd)) {
                    targs.push(self.parseTypeRef());
                    self.eat(Tok.Comma);
                }
                self.closeAngle();
            }
            // A parameterized trait is a template, not a type. `Iter` alone does not say what
            // `next` returns, so naming it without arguments is refused rather than resolved to
            // one arbitrary instantiation, and giving arguments to a trait that takes none names
            // an instance nobody declared.
            want: long = gReg.traitDef(ti).paramCount;
            if (want > 0 && targs.len() == 0) {
                self.err(format("missing type arguments for trait `{}`\nhelp: write `{}<...>`",
                                spelling, spelling));
            }
            if (want == 0 && targs.len() > 0) {
                self.err(format("trait `{}` takes no type arguments", spelling));
            }
            return TypeRef { base: Lit.TraitObj, name: regStampTrait(q, targs) };
        }
        if (self.check(Tok.LessThan)) { return self.parseGenericArgs(q); }
        if (gReg.isGenericSym(q)) { return self.defaultInstance(q); }
        // A type alias is a second spelling of a type, not a type of its own. Expanding it here,
        // the one place a type is read, is what keeps every later phase from having to know
        // aliases exist: `AtomicInt` becomes `Atomic_int`, with its size, fields and methods.
        al: long = gReg.findAlias(nameOf(q));
        if (al >= 0) { return gReg.aliasDef(al).target; }
        // Nothing declares it. Said as it is read, naming what was written: left to resolve
        // itself later it becomes a struct with no fields and no size, and what gets reported is
        // whichever offset or copy that silence eventually breaks.
        if (self.inPointee == 0 && !gReg.declares(nameOf(q))) {
            self.err(format("cannot find type `{}` in this scope", written));
        }
        return TypeRef { base: Lit.Struct, name: q };
    }
}

// A string literal without its surrounding quotes. The token keeps them (that is what makes the
// token stream a faithful record of the source) but nothing downstream wants them.
pub unquoted t:Sym -> Sym {
    s: str = nameOf(t);
    if (s.len >= 2 && charAt(s, 0) == '"') { return intern(strSlice(s, 1, s.len - 2)); }
    return t;
}

// What a store can go to: a variable, a field, an element, or what a pointer points at.
pub isPlaceOp op:Op -> bool {
    return op == Op.Lvalue || op == Op.FieldAccess || op == Op.ArrayIndex || op == Op.Deref;
}

// What the target of a store is, said the way a refusal names it, for one that is not a place:
// "a tuple expression", "the result of a call to `f`", "the result of `+`".
pub nonPlaceText a:Ast id:NodeId -> String {
    e: Expr = a.expr(id);
    o: Op = e.op;
    if (o == Op.TupleLit) { return stringOf("a tuple expression"); }
    if (o == Op.StructLit) { return stringOf("a struct literal"); }
    if (o == Op.ArrayLit) { return stringOf("an array literal"); }
    if (o == Op.Literal || o == Op.StringLit) { return stringOf("a literal"); }
    if (o == Op.Cast) { return stringOf("a cast"); }
    if (o == Op.FunctionCall || o == Op.MethodCall || o == Op.MacroCall) {
        callee: str = "";
        match e.payload { Call(ix) { callee = sourceName(a.calls.get(ix).name); } _ { } }
        if (o == Op.MacroCall) { return format("the result of `{}!`", callee); }
        if (callee.len == 0) { return stringOf("the result of a call"); }
        return format("the result of a call to `{}`", callee);
    }
    if (o == Op.AddressOf) { return stringOf("an address"); }
    if (o == Op.Assignment) { return stringOf("an assignment"); }
    if (o == Op.Sizeof || o == Op.Nameof) { return format("the result of `{}`", opName(o)); }
    if (e.left != NO_NODE || o == Op.LogicalNot || o == Op.BitwiseNot) { return format("the result of `{}`", opName(o)); }
    return stringOf("this expression");
}

// A name as its declaration spelled it: without the module a top-level name is qualified with,
// or the `$n` a shadowing local was renamed with.
local sourceName n:Sym -> str {
    s: str = nameOf(n);
    from: long = 0;
    for i in 0..s.len {
        if (i + 1 < s.len && charAt(s, i) == ':' && charAt(s, i + 1) == ':') { from = i + 2; }
    }
    to: long = s.len;
    for i in from..s.len { if (charAt(s, i) == '$' && to == s.len) { to = i; } }
    return strSlice(s, from, to - from);
}

// Where each operator sits on the ladder: higher binds tighter. Leaves and the prefix operators
// bind tightest, so a new operator is always built above them and never descends into one.
pub precedenceOf op:Op -> long {
    if (op == Op.Assignment) { return 0; }
    if (op == Op.LogicalOr)  { return 1; }
    if (op == Op.LogicalAnd) { return 2; }
    if (op == Op.BitwiseOr)  { return 3; }
    if (op == Op.BitwiseXor) { return 4; }
    if (op == Op.BitwiseAnd) { return 5; }
    if (op == Op.IsEqual || op == Op.IsNotEqual || op == Op.IsLessOrEqual
        || op == Op.IsGreaterOrEqual || op == Op.LessThan || op == Op.GreaterThan) { return 6; }
    if (op == Op.ShiftLeft || op == Op.ShiftRight) { return 7; }
    if (op == Op.Addition || op == Op.Subtraction) { return 8; }
    if (op == Op.Multiplication || op == Op.Division || op == Op.Modulus) { return 9; }
    return 11;
}

methods Parser {
    // ─── statements ──────────────────────────────────────────────────────────

    // A `{ ... }` block. Its own scope, so a local declared inside is gone after it.
    parseBlock &self -> long {
        self.expect(Tok.LeftCurly);
        self.pushScope();
        ids: Vec<long> = self.parseStmtsUntilClose();
        self.popScope();
        return self.ast.addBlock(ids);
    }

    // Statements up to the closing brace, which this consumes. Collected locally and appended by
    // the caller in one block, so this block's run stays contiguous while nested blocks append
    // theirs first.
    parseStmtsUntilClose &self -> Vec<long> {
        ids: Vec<long>;
        // A queued initializer belongs to the block that declared it, so the queue is drained
        // before the brace closes. Stopping at the brace would leave the last declaration's store
        // behind for the enclosing block's next statement to hand back, so
        // `if (c) { a: long = 1; }` would run the store unconditionally, writing a variable scoped
        // to the inner block. Only a block's last declaration is at risk, because every earlier
        // one has a following statement to be handed back at.
        going: bool = true;
        while (going) {
            if (self.pendingInits.len() == 0
                && (self.check(Tok.RightCurly) || self.check(Tok.FileEnd))) { going = false; }
            else {
                ids.push(self.parseStatement());
                // `x: T = f()?;`: the rest of the block is the `else` that continues (`contIf`).
                if (self.contIf >= 0) {
                    at: long = self.contIf;
                    body: Vec<long>;
                    body.extend(self.contPre);
                    self.contIf = -1;
                    body.extend(self.parseStmtsUntilClose());
                    nd: IfNode = self.ast.ifs.get(at);
                    nd.body = self.ast.addBlock(body);
                    self.ast.ifs.set(at, nd);
                    return ids;
                }
            }
        }
        self.expect(Tok.RightCurly);
        return ids;
    }

    // What a call yields, when the callee has already been parsed. A forward reference or a
    // mutually recursive call has no answer yet and takes a placeholder the checker overwrites:
    // `int`, matching what every other unknown starts as.
    calleeReturn &self bare:Sym -> Lit {
        hit: Option<Lit> = self.fnReturns.find(nameOf(bare));
        match hit { Some(k) { return k; } None { } }
        return Lit.Int;
    }

    // Every statement stands where its first token does. That is in force while it is read, so
    // what the parser writes on its behalf (a `match` arm's bindings, a declaration's store)
    // stands there too, and is put back after it, for whatever encloses it. The statement itself
    // is made last (an `if` after its body), so it is stamped when it is done.
    parseStatement &self -> long {
        // A declaration's initializer, queued by the declaration it came from, which it stands at.
        if (self.pendingInits.len() > 0) {
            st: long = self.pendingInits.get(0);
            self.pendingInits.removeAt(0);
            return st;
        }
        was: long = gPos;
        start: long = self.curPos;
        gPos = start;
        mark: long = self.tryHole.len();
        id: long = self.parseStatementHere();
        if (self.tryHole.len() > mark) {
            id = self.wrapTries(id, mark);
            while (self.tryHole.len() > mark) { self.tryHole.pop(); self.tryOperand.pop(); self.tryName.pop(); }
        }
        self.ast.stmtPos.set(id, start);
        gPos = was;
        self.lastStmt = id;
        return id;
    }

    parseStatementHere &self -> long {
        // `{ ... }` on its own: a scope, run once, for fencing off a working variable. The same
        // node an `unsafe` block uses; only that one grants anything.
        if (self.check(Tok.LeftCurly)) {
            self.ast.blockStmts.push(BlockStmtNode { body: self.parseBlock() });
            return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
        }
        if (self.check(Tok.Id)) {
            if ((self.word("if") && !self.namedHere()))       { self.advance(); return self.parseIf(); }
            if ((self.word("while") && !self.namedHere()))    { self.advance(); return self.parseWhile(); }
            if ((self.word("loop") && !self.namedHere()))     { self.advance(); return self.parseLoop(); }
            if ((self.word("return") && !self.namedHere()))   { self.advance(); return self.parseReturn(); }
            if ((self.word("break") && !self.namedHere()))    { self.advance(); return self.parseJump(StmtKind.Break, "break"); }
            if ((self.word("continue") && !self.namedHere())) { self.advance(); return self.parseJump(StmtKind.Continue, "continue"); }
            if ((self.word("methods") && !self.namedHere()))  { self.advance(); return self.parseMethodsBlock(); }
            if ((self.word("trait") && !self.namedHere()))    { self.advance(); return self.parseTraitDecl(); }
            if ((self.word("type") && !self.namedHere()))     { self.advance(); return self.parseTypeAlias(); }
            if ((self.word("with") && !self.namedHere()))     { self.advance(); return self.parseWith(); }
            if ((self.word("struct") && !self.namedHere()))   { self.advance(); return self.parseStructDecl(); }
            if ((self.word("enum") && !self.namedHere()))     { self.advance(); return self.parseEnumDecl(); }
            if ((self.word("match") && !self.namedHere()))    { self.advance(); return self.parseMatch(); }
            if ((self.word("for") && !self.namedHere()))      { self.advance(); return self.parseFor(); }
            if ((self.word("unsafe") && !self.namedHere()))   { self.advance(); return self.parseUnsafe(); }
            if ((self.word("recover") && !self.namedHere()))  { self.advance(); return self.parseRecover(); }
            if ((self.word("asm") && !self.namedHere()))      { self.advance(); return self.parseAsmBlock(); }
            // `assert!(cond);` is a statement macro. The `!` is what marks a macro call, so a
            // function named `assert` is still an ordinary call.
            if (self.word("assert") && self.peekNext().kind == Tok.Exclamation
                && !gReg.isMacro(self.resolveHere("assert"))) {
                self.advance();
                return self.parseAssert();
            }
            return self.parseFromName();
        }
        // Inside a quote `@x` is a splice, an expression.
        if (self.check(Tok.AtSign) && self.quoteDepth > 0) {
            lhs: NodeId = self.parseAtom();
            return self.finishAssignOrExpr(lhs);
        }
        if (self.check(Tok.AtSign)) {
            self.err(stringOf("unexpected `@` outside a `quote`\nnote: `@x` splices a Node into a quote\nhelp: a macro is called as `name!(...)`"));
        }
        if (self.check(Tok.Star)) {              // *p = v: a store through a pointer
            lhs: NodeId = self.parseAtom();
            return self.finishAssignOrExpr(lhs);
        }
        // An expression statement that opens with a literal or a parenthesis: `"ab".m();`,
        // `(a + b).show();`, `5.inc();`. Inside a body only, where a statement may be one.
        if (self.fnDepth > 0 && (self.check(Tok.StringLiteral) || self.check(Tok.IntLiteral)
                                 || self.check(Tok.LongLiteral) || self.check(Tok.U64Literal) || self.check(Tok.CharLiteral) || self.check(Tok.FloatLiteral)
                                 || self.check(Tok.Literal) || self.check(Tok.LeftParen))) {
            return self.finishAssignOrExpr(self.parseExpr());
        }
        // `{ x } = 1;`, `if (c) { a } else { b } = 1;`: a block, an `if`, a `match` or a loop is a
        // statement here and yields no value, so what follows it cannot store into it.
        if (self.check(Tok.Equals) && self.lastStmt >= 0) {
            k: StmtKind = self.ast.stmts.get(self.lastStmt).kind;
            what: str = "";
            if (k == StmtKind.Block) { what = "a block"; }
            else if (k == StmtKind.If) { what = "an `if`"; }
            else if (k == StmtKind.Match) { what = "a `match`"; }
            else if (k == StmtKind.Unsafe) { what = "an `unsafe` block"; }
            else if (k == StmtKind.Recover) { what = "a `recover`"; }
            else if (k == StmtKind.While || k == StmtKind.Loop) { what = "a loop"; }
            if (what.len > 0) {
                self.err(format("cannot assign to {}\nnote: it is a statement and yields no value, so a store has nothing to go to\nhelp: assign inside it (`{{ x = v; }}`), or to a variable it sets", what));
            }
        }
        self.err(format("expected a statement, found {}", describeTok(self.cur)));
        return 0;
    }

    parseIf &self -> long {
        self.expect(Tok.LeftParen);
        cond: NodeId = self.parseExpr();
        self.expect(Tok.RightParen);
        body: long = self.parseBlock();
        chain: long = -1;
        if (self.eatWord("else")) {
            if (self.eatWord("if")) { chain = self.ifNodeOf(self.parseIf()); }
            else {
                elseBody: long = self.parseBlock();
                // A bare `else` is the last link of the chain with a condition that always holds,
                // rather than a link with no condition: one shape means every walker asks the
                // same question, and the constant folds away before anything is emitted.
                always: NodeId = self.ast.leaf(Op.Literal, Payload.Num(1), Lit.Bool);
                self.ast.ifs.push(IfNode { cond: always, body: elseBody, elseIf: -1 });
                chain = self.ast.ifs.len() - 1;
            }
        }
        self.ast.ifs.push(IfNode { cond: cond, body: body, elseIf: chain });
        return self.ast.addStmt(StmtKind.If, self.ast.ifs.len() - 1);
    }
    // The IfNode a just-parsed `if` statement wraps, so an `else if` can chain onto it.
    ifNodeOf &self stmt:long -> long { return self.ast.stmts.get(stmt).at; }

    parseWhile &self -> long {
        self.expect(Tok.LeftParen);
        cond: NodeId = self.parseExpr();
        self.expect(Tok.RightParen);
        self.loopDepth = self.loopDepth + 1;
        body: long = self.parseBlock();
        self.loopDepth = self.loopDepth - 1;
        self.ast.whiles.push(WhileNode { cond: cond, body: body, step: -1 });
        return self.ast.addStmt(StmtKind.While, self.ast.whiles.len() - 1);
    }

    parseLoop &self -> long {
        self.loopDepth = self.loopDepth + 1;
        body: long = self.parseBlock();
        self.loopDepth = self.loopDepth - 1;
        self.ast.blockStmts.push(BlockStmtNode { body: body });
        return self.ast.addStmt(StmtKind.Loop, self.ast.blockStmts.len() - 1);
    }

    // `recover { body } else { handler }`. The handler is not optional: a `recover` that
    // swallows a `raise` and says nothing about it is better written with an empty one, where
    // the reader can see it.
    parseRecover &self -> long {
        if (!self.check(Tok.LeftCurly)) {
            self.err(format("expected `{{` after `recover`, found {}\nhelp: write `recover {{ ... }} else {{ ... }}`", describeTok(self.cur)));
        }
        body: long = self.parseBlock();
        if (!self.eatWord("else")) {
            self.err(format("expected `else` after the body of a `recover`, found {}\nnote: the `else` block is where a `raise` under the body resumes\nhelp: write `recover {{ ... }} else {{ ... }}`", describeTok(self.cur)));
        }
        handler: long = self.parseBlock();
        self.ast.whiles.push(WhileNode { cond: NO_NODE, body: body, step: handler });
        return self.ast.addStmt(StmtKind.Recover, self.ast.whiles.len() - 1);
    }

    parseReturn &self -> long {
        v: NodeId = NO_NODE;
        if (!self.check(Tok.Semicolon)) { v = self.parseExpr(); }
        self.expect(Tok.Semicolon);
        self.ast.returns.push(ReturnNode { value: v });
        return self.ast.addStmt(StmtKind.Return, self.ast.returns.len() - 1);
    }

    // Refused here rather than lowered into a jump with no target: the enclosing loop is
    // positional, so this is the only place that knows whether there is one.
    parseJump &self k:StmtKind what:str -> long {
        self.eat(Tok.Semicolon);
        if (self.loopDepth == 0) {
            self.err(format("`{}` outside of a loop", what));
        }
        return self.ast.addStmt(k, 0);
    }

    // A statement that begins with an identifier: a declaration, an assignment, a call, or a
    // function definition. Which one is decided by what follows the name.
    parseFromName &self -> long {
        name: Token = self.advance();

        // `_ = f();` evaluates and discards; `_, b = t;` and `a, _ = t;` discard an element.
        if (nameOf(name.text) == "_" && self.bindingOf(name.text).renamed == NO_SYM && self.fnDepth > 0) {
            if (self.check(Tok.Equals)) { return self.parseDiscard(); }
            if (self.check(Tok.Comma)) {
                nx: Token = self.peekNext();
                if (nx.kind == Tok.Id && nameOf(nx.text) != "_" && self.bindingOf(nx.text).renamed == NO_SYM) {
                    return self.parseDestructure(name.text);
                }
                return self.parseDestructureInto(NO_NODE, NO_SYM);
            }
        }

        if (self.check(Tok.Colon)) {
            self.advance();
            if (self.fnDepth == 0) { return self.parseGlobal(name.text, self.vis); }
            return self.parseVarDecl(name.text);
        }

        // `q, r = tupleCall();`: a tuple taken apart into fresh locals, or, when the names are
        // locals already, assigned into them (`leaf, pos = db.advance(leaf, pos);`).
        if (self.check(Tok.Comma)) {
            if (self.bindingOf(name.text).renamed == NO_SYM) { return self.parseDestructure(name.text); }
            return self.parseDestructureInto(self.parseNamedFrom(name), name.text);
        }

        // `name<T> ...`: a generic function template.
        if (self.check(Tok.LessThan) && self.fnDepth == 0) {
            return self.parseGenericFunction(name.text);
        }
        // `name args -> type { }` or `name -> type { }`: a function definition. Not `x as T`,
        // which no parameter list can start with: a cast, the start of an expression.
        castNext: bool = self.fnDepth > 0 && self.word("as") && !self.namedHere();
        if (self.check(Tok.Arrow) || (self.check(Tok.Id) && !castNext)) { return self.parseFunctionDef(name.text); }

        lhs: NodeId = self.parseNamedFrom(name);
        // `a + b = 3`: an operator after the name's chain. Read to the expression's end, so a
        // store to it is refused as one; anything else is the error it always was, a statement
        // cannot go on past the name.
        if (self.fnDepth > 0 && self.peekBinOp() != Op.Literal) {
            opAt: long = self.curPos;
            op: Token = self.cur;
            full: NodeId = self.continueExpr(lhs);
            if (self.check(Tok.Equals) || self.compoundOp() != Op.Literal) { return self.finishAssignOrExpr(full); }
            self.errAt(opAt, format("expected a statement, found {}", describeTok(op)));
        }
        return self.finishAssignOrExpr(lhs);
    }

    // An assignment to the place just parsed, or a bare expression statement.
    finishAssignOrExpr &self lhs:NodeId -> long {
        // Where the statement, and so the target, begins.
        at: long = gPos;
        // `self.leaf, pos = ...`: a destructure whose first target is a place, not a bare name.
        // Nothing else may stand before a comma at the start of a statement.
        if (self.check(Tok.Comma)) {
            if (self.isPlace(lhs)) { return self.parseDestructureInto(lhs, NO_SYM); }
            self.refuseNonPlace(lhs, at, stringOf("a destructure assigns to places: a local, a field, an element or `*p`"));
        }
        cop: Op = self.compoundOp();
        if (cop != Op.Literal) {
            self.refuseNonPlace(lhs, at, format("`{}=` stores into its left side, which has to be a place: a local, a field, an element or `*p`", opName(cop)));
            self.advance();
            rhs: NodeId = self.parseExpr();
            self.expect(Tok.Semicolon);
            return self.compoundAssign(lhs, cop, rhs);
        }
        if (self.check(Tok.Equals)) {
            self.refuseNonPlace(lhs, at, stringOf("a store needs a place: a local, a field, an element or `*p`"));
            self.advance();
            rhs: NodeId = self.parseExpr();
            self.expect(Tok.Semicolon);
            // The wider of the two, as every other operator is typed here: the store's width is
            // the target's and the checker settles it, so the parse-time type is the same
            // placeholder an addition carries and is spelled the same way.
            k: Lit = higherPrecedence(self.ast.expr(lhs).kind, self.ast.expr(rhs).kind);
            e: NodeId = self.ast.binary(Op.Assignment, lhs, rhs, k);
            self.ast.exprStmts.push(ExprStmtNode { value: e });
            return self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1);
        }
        self.eat(Tok.Semicolon);
        // `f(args);`: the result is discarded, so the call carries no type. `calleeReturn`'s
        // guess is for a call whose value is used, and keeping it here would claim a statement
        // yields something.
        e: Expr = self.ast.expr(lhs);
        if (e.op == Op.FunctionCall) {
            e.kind = Lit.Void;
            self.ast.setExpr(lhs, e);
        }
        self.ast.exprStmts.push(ExprStmtNode { value: lhs });
        return self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1);
    }

    // `name: T;`, `name: T = v;`, `name: [T; N];` or `name: [T];`. The colon is already consumed.
    //
    // `[T; N]` is an array: storage. `[T]` is a slice: a {ptr, len} view of storage someone else
    // owns. What follows the element type is what tells them apart.
    parseVarDecl &self name:Sym -> long {
        kind: Lit = Lit.Void;
        sname: Sym = NO_SYM;
        isArray: bool = false;
        count: long = 0;
        elemKind: Lit = Lit.Void;
        elemStruct: Sym = NO_SYM;

        if (self.check(Tok.LeftSquare)) {
            self.advance();
            elem: TypeRef = self.parseTypeRef();
            if (self.eat(Tok.Semicolon)) {
                count = self.parseArrayLength();
                self.expect(Tok.RightSquare);
                isArray = true;
                kind = elem.base;
                sname = elem.name;
            } else {
                self.expect(Tok.RightSquare);
                kind = Lit.Slice;
                sname = intern(sliceElemName(elem.base, elem.name));
                elemKind = elem.base;
                elemStruct = elem.name;
            }
        } else {
            t: TypeRef = self.parseTypeRef();
            kind = t.base;
            sname = t.name;
        }

        renamed: Sym = self.declareLocal(name, kind, sname);
        if (isArray) {
            b: Binding = self.scopes.pop();
            b.isArray = true;
            self.scopes.push(b);
        }
        init: NodeId = NO_NODE;
        if (self.eat(Tok.Equals)) { init = self.parseExpr(); }
        self.expect(Tok.Semicolon);

        // `n: long = 0;` is a declaration and an assignment, and it is written out as both: the
        // initializer becomes an ordinary store, so definite-init, moves and lowering all see the
        // one shape they already handle rather than a second one hiding in the declaration. The
        // assignment is queued and handed back by the next `parseStatement`, since a statement is
        // returned one at a time.
        self.ast.decls.push(VarDeclNode { name: renamed, kind: kind, structName: sname,
                                          isArray: isArray, count: count, conv: Conv.None,
                                          isVariadic: false, elemKind: elemKind,
                                          elemStruct: elemStruct, init: NO_NODE });
        decl: long = self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1);
        // `xs: [T; N] = [a, b, ...]`: one store per element, `xs[0] = a; xs[1] = b; ...`, each
        // the ordinary store to an element (held to T, an owning value moved in), after the
        // declaration has zeroed the array or built its `Default` elements.
        if (init != NO_NODE && self.ast.expr(init).op == Op.ArrayLit) {
            ln: LitNode = self.arrayLitFor(init, isArray, count);
            for k in 0..ln.initCount {
                self.ast.indexes.push(IndexNode { name: NO_SYM, base: self.nameRef(renamed, kind, sname),
                                                  index: self.numberLit(k, Lit.Long), whole: false,
                                                  rawPointerBase: false, sliceStart: NO_NODE,
                                                  sliceEnd: NO_NODE, at: NO_SYM });
                el: NodeId = self.ast.leaf(Op.ArrayIndex, Payload.Index(self.ast.indexes.len() - 1), kind);
                v: NodeId = self.ast.inits.get(ln.firstInit + k).value;
                asn: NodeId = self.ast.binary(Op.Assignment, el, v, higherPrecedence(kind, self.ast.expr(v).kind));
                self.ast.exprStmts.push(ExprStmtNode { value: asn });
                self.pendingInits.push(self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1));
            }
            return decl;
        }
        if (init != NO_NODE) {
            target: NodeId = self.ast.leafOf(Op.Lvalue, Payload.Name(renamed), kind, sname);
            asn: NodeId = self.ast.binary(Op.Assignment, target, init,
                                          higherPrecedence(kind, self.ast.expr(init).kind));
            self.ast.exprStmts.push(ExprStmtNode { value: asn });
            self.pendingInits.push(self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1));
        }
        return decl;
    }

    // `name arg:T arg2:T -> Ret { }`. The name is already consumed.
    parseFunctionDef &self name:Sym -> long {
        // Named before the body is parsed: the lexer crosses into the next file while reading the
        // body, and asking afterwards qualifies with the wrong module.
        q: Sym = self.qualify(nameOf(name));
        file: Sym = self.lx.currentFile;
        pkg: Sym = self.lx.currentPackage;
        self.pushScope();
        attrs: long = self.fnAttrs;
        self.fnAttrs = 0;
        params: Vec<long> = self.parseParams();
        self.expect(Tok.Arrow);
        ret: TypeRef = self.parseRetType();
        if (self.retNever) { attrs = attrs | FN_NEVER; }
        // Recorded before the body, so a recursive call inside it already knows what it yields.
        // It is keyed by the qualified name, as the earlier compiler keyed it, so a bare call site
        // does not find it and falls back to the placeholder. That keeps the tree the same shape
        // the earlier compiler built.
        if (!self.fnReturns.has(nameOf(q))) { self.fnReturnsAdded.push(q); }
        regFnReturn(&self.fnReturns, q, ret.base, pkg);
        // `name a:T -> R;`, declared, not defined: the body is in another object and the linker
        // will find it. A body of -1 is what says so, and every pass that walks one already asks
        // (`checkReturns`, `checkReturnedViews`, the lowerer). Only a `pub` declaration means
        // anything: `local` and `pkg` are internal to this object, so a name nothing here defines
        // is a name nothing can ever call.
        body: long = -1;
        if ((attrs & FN_BUILTIN_DECL) != 0) {
            attrs = (attrs & ~FN_BUILTIN_DECL) | (self.builtinKind(nameOf(name), params, ret, attrs) << BUILTIN_SHIFT);
            self.expect(Tok.Semicolon);
        } else if (self.check(Tok.Semicolon)) {
            self.advance();
            if (self.vis != Vis.Pub) {
                self.err(format("function `{}` has no body\nnote: a declaration without a body names a function defined in another object\nhelp: declare it `pub`",
                                nameOf(name)));
            }
        } else {
            self.fnDepth = self.fnDepth + 1;
            was: Sym = gReg.deferIn;
            wasPlain: bool = self.plainBody;
            self.plainBody = self.typeVars.len() == 0;
            if (self.typeVars.len() == 0 && isUpstreamPkg(pkg)) { gReg.deferIn = file; }
            wasRet: TypeRef = self.retTy;
            wasRetOk: bool = self.retOk;
            self.retTy = ret;
            self.retOk = true;
            body = self.parseBlock();
            self.retTy = wasRet;
            self.retOk = wasRetOk;
            gReg.deferIn = was;
            self.plainBody = wasPlain;
            self.fnDepth = self.fnDepth - 1;
        }
        self.popScope();

        first: long = self.ast.addParams(params);
        self.ast.fns.push(FnNode { name: q,
                                   returnKind: ret.base, returnStruct: ret.name,
                                   // The visibility as written (`pub`, `pkg` or `local`),
                                   // which is what the visibility checks read.
                                   visibility: self.vis,
                                   file: file, pkg: pkg,
                                   isUnsafe: false, isTemplate: false, inferReturn: false,
                                   firstBound: self.boundFirst, boundCount: self.boundCount,
                                   firstArg: first, argCount: params.len(), body: body, attrs: attrs });
        return self.ast.addStmt(StmtKind.FunctionDef, self.ast.fns.len() - 1);
    }

    // A function's result type, or `never`: a function that does not come back, its result
    // `void` with `FN_NEVER` on the declaration (`retNever`). `never` is a word only here: a type
    // of that name is still a type everywhere else, and one declared in scope wins.
    parseRetType &self -> TypeRef {
        self.retNever = false;
        if (self.word("never") && self.typeNameOwner("never").len == 0) {
            self.advance();
            self.retNever = true;
            return typeRefOf(Lit.Void);
        }
        return self.parseTypeRef();
    }

    // `builtin name params -> T;`: a declaration whose body the compiler provides. The primitive
    // is the one its declaration names. The library's declaration is the contract, visible where
    // it stands, and calls reach it by ordinary name resolution like any function's. The
    // signature is held to what the compiler provides, so a wrong one is refused here rather
    // than miscompiled.
    builtinKind &self n:str params:Vec<long> ret:TypeRef attrs:long -> long {
        if (self.fnDepth > 0 || self.typeVars.len() > 0) {
            self.err(format("`builtin {}` must be declared at the top level and cannot be generic", n));
        }
        k: long = 0;
        want: str = "";
        ok: bool = false;
        np: long = params.len();
        if (n == "syscall") {
            k = BI_SYSCALL;
            want = "unsafe builtin syscall nr:long args:...long -> long";
            ok = np == 2 && self.paramIs(params.get(0), Lit.Long, false) && self.paramIs(params.get(1), Lit.Long, true)
                 && ret.base == Lit.Long;
        } else if (n == "atCompileTime") {
            k = BI_AT_COMPILE_TIME;
            want = "builtin atCompileTime -> bool";
            ok = np == 0 && ret.base == Lit.Bool;
        } else if (n == "parseExpr") {
            k = BI_PARSE_EXPR;
            want = "builtin parseExpr src:str -> Node";
            ok = np == 1 && self.paramIs(params.get(0), Lit.Str, false) && ret.base == Lit.Struct;
        } else if (n == "exit") {
            k = BI_EXIT;
            want = "builtin exit status:long -> never";
            ok = np == 1 && self.paramIs(params.get(0), Lit.Long, false) && (attrs & FN_NEVER) != 0;
        } else if (atomicBuiltinOf(n) != 0) {
            k = atomicBuiltinOf(n);
            // The word is a `long`, or an `int` for the `32` forms: every operand and the result
            // are of that type, and the address points at one.
            w: Lit = Lit.Long;
            if (k >= BI_ATOMIC_LOAD + BI_ATOMIC_32) { w = Lit.Int; }
            ws: str = typeName(w);
            op: long = atomicOpOf(k);
            values: long = 1;
            if (op == BI_ATOMIC_LOAD) { values = 0; }
            if (op == BI_ATOMIC_CAS) { values = 2; }
            gives: bool = op != BI_ATOMIC_STORE && op != BI_ATOMIC_STORE_SC;
            ok = np == values + 1 && self.paramIsPtr(params.get(0), ws);
            for j in 1..np { if (ok && !self.paramIs(params.get(j), w, false)) { ok = false; } }
            if (gives) { ok = ok && ret.base == w; } else { ok = ok && ret.base == Lit.Void; }
            s: String;
            s.pushStr("unsafe builtin ");
            s.pushStr(n);
            s.pushStr(" p:*");
            s.pushStr(ws);
            if (op == BI_ATOMIC_CAS) { s.pushStr(" expected:"); s.pushStr(ws); s.pushStr(" desired:"); s.pushStr(ws); }
            else if (values == 1) { s.pushStr(" v:"); s.pushStr(ws); }
            s.pushStr(" -> ");
            if (gives) { s.pushStr(ws); } else { s.pushStr("void"); }
            want = keepString(s);
        } else if (n == "memcpy") {
            k = BI_MEMCPY;
            want = "unsafe builtin memcpy dst:long src:long n:long -> void";
            ok = np == 3 && self.paramIs(params.get(0), Lit.Long, false) && self.paramIs(params.get(1), Lit.Long, false)
                 && self.paramIs(params.get(2), Lit.Long, false) && ret.base == Lit.Void;
        } else {
            self.err(format("the compiler provides no builtin `{}`\nnote: the builtins are `syscall`, `atCompileTime`, `parseExpr`, `exit`, `memcpy`, and the atomics `atomicLoad`, `atomicStore`, `atomicStoreSeqCst`, `atomicSwap`, `atomicCas` and `atomicAdd` (each with a `32` form)", n));
        }
        if (!ok) { self.err(format("wrong signature for `builtin {}`\nhelp: declare it as `{}`", n, want)); }
        return k;
    }
    // A parameter `*T`, `T` the scalar spelled `scalar`.
    paramIsPtr &self at:long scalar:str -> bool {
        d: VarDeclNode = self.ast.decls.get(at);
        return !d.isVariadic && !d.isArray && d.kind == Lit.Ptr && d.structName != NO_SYM && nameOf(d.structName) == scalar;
    }
    paramIs &self at:long k:Lit variadic:bool -> bool {
        d: VarDeclNode = self.ast.decls.get(at);
        if (variadic) { return d.isVariadic && d.elemKind == k; }
        return !d.isVariadic && d.kind == k && !d.isArray;
    }

    // Parameters up to the arrow, each `name:Type`. Declared into the scope the caller opened, so
    // the body can name them.
    parseParams &self -> Vec<long> { return self.parseParamList(false); }

    // `traitSig`: a trait method's parameters, where the convention is written after the colon
    // (`v: sink T`) rather than before the name (`sink v: T`). A trait says how it hands a
    // parameter over as part of the contract, so it reads as part of the type; a function says
    // it about its own parameter, so it reads as part of the declaration.
    parseParamList &self traitSig:bool -> Vec<long> {
        out: Vec<long>;
        while (self.check(Tok.Id)) {
            // An explicit convention. `inout` is the only one that must be written (the compiler
            // infers `read` versus `sink` from what the body does with the parameter) but all
            // three are accepted where they are spelled.
            //
            // A trait's signature takes them in either place: before the name, as a function
            // writes them (`inout v:Vec<long>`), or after the colon, as a fn type does
            // (`r:sink Res`, `v:inout Vec<long>`). A word followed by `:` is the parameter's name.
            conv: Conv = Conv.None;
            if (self.peekNext().kind != Tok.Colon) {
                if (self.eatWord("inout"))     { conv = Conv.Inout; }
                else if (self.eatWord("read")) { conv = Conv.Read; }
                else if (self.eatWord("sink")) { conv = Conv.Sink; }
            }

            pname: Token = self.expect(Tok.Id);
            self.expect(Tok.Colon);
            if (traitSig && conv == Conv.None && self.peekNext().kind != Tok.Colon) {
                if (self.eatWord("read"))       { conv = Conv.Read; }
                else if (self.eatWord("sink"))  { conv = Conv.Sink; }
                else if (self.eatWord("inout")) { conv = Conv.Inout; }
            }

            // `...T` collects the trailing arguments into a `[T]` the callee sees as a slice.
            variadic: bool = self.eat(Tok.Ellipsis);
            // `other: Self` in a trait signature names the implementing type, the same word the
            // return position already keeps as itself. It is not a type this file declares, and
            // resolving it would qualify it with whichever module the trait was written in.
            t: TypeRef = TypeRef { base: Lit.Struct, name: intern("Self") };
            if (traitSig && self.word("Self")) { self.advance(); }
            else { t = self.parseTypeRef(); }
            kind: Lit = t.base;
            sname: Sym = t.name;
            elemKind: Lit = Lit.Void;
            elemStruct: Sym = NO_SYM;
            if (variadic) {
                elemKind = t.base;
                elemStruct = t.name;
                kind = Lit.Slice;
                sname = intern(sliceElemName(t.base, t.name));
            }
            // `inout` on a struct is a borrow: a pointer to it. On a slice it is not: a slice is
            // already a fat pointer, and `inout` only says the callee may write through it. Making
            // one a ref loses the length and leaves `.ptr`/`.len` reading the slot's own address.
            //
            // On anything else it says nothing at all: a scalar is already the callee's own copy,
            // and a variadic is a slice the call built rather than one the caller can see written.
            // An annotation with no meaning is refused rather than ignored.
            //
            // A type parameter is exempt, and has to be: `count<T, I: Iter<T>> inout it:I` says
            // exactly what it means, and what `I` turns out to be is not known until an instance
            // is stamped.
            checkable: bool = !traitSig && kind != Lit.TypeVar;
            // `inout x:long`: a lend of the caller's scalar (`INOUT_SCALAR`).
            if (conv == Conv.Inout && !variadic && (isInteger(kind) || isFloat(kind) || kind == Lit.Bool
                                                    || namedScalar(kind, sname))) {
                sname = inoutScalarName(kind, sname);
                kind = Lit.Ref;
            }
            if (checkable && conv == Conv.Inout && !isInoutScalarName(sname)) {
                borrowable: bool = kind == Lit.Slice && !variadic;
                if ((kind != Lit.Struct && !borrowable) || variadic) {
                    self.err(format("`inout` cannot apply to parameter `{}`\nnote: `inout` lends a struct, a slice or a scalar, and never a variadic parameter",
                                    nameOf(pname.text)));
                }
            }
            if (checkable && (conv == Conv.Read || conv == Conv.Sink) && kind != Lit.Struct) {
                self.err(stringOf("`read` and `sink` apply only to struct parameters\nnote: anything else is already passed by value"));
            }
            if (conv == Conv.Inout && kind == Lit.Struct) { kind = Lit.Ref; }

            renamed: Sym = self.declareLocal(pname.text, kind, sname);
            self.ast.decls.push(VarDeclNode { name: renamed, kind: kind, structName: sname,
                                              isArray: false, count: 0, conv: conv,
                                              isVariadic: variadic, elemKind: elemKind,
                                              elemStruct: elemStruct, init: NO_NODE });
            out.push(self.ast.decls.len() - 1);
        }
        return out;
    }

    // A program is read a module at a time, in the scanner's order: `beginModule` puts the lexer on
    // one module's text, `parseModule` reads its top-level statements onto the page, and
    // `finishPage` reads the macros met on the way and closes the page. A module read from a
    // `.klib` is not parsed at all; its statements are put on the page already built
    // (`notePage`, `noteLoadedMacro`), so a module's tree never depends on the text around it.
    beginModule &self text:str mod:long -> void {
        self.lx = lexerOf(text);
        self.hasPeeked = false;
        self.curMod = mod;
        opsModule(mod);
        gReg.journal = true;
        self.advance();
    }

    // The whole program as one text with its `#file` markers: what `--emit=tokens` and the
    // evaluator's own parser see.
    parsePage &self -> long {
        self.parseModule();
        return self.finishPage();
    }

    parseModule &self -> void {
        while (!self.check(Tok.FileEnd)) {
            if (canRecover()) { self.parseDeclRecovering(); } else { self.parseDecl(); }
        }
        self.checkImplTraits();
    }

    // One top-level declaration, onto the page.
    parseDecl &self -> void {
        // Each declaration's local names are numbered from zero, so its tree is the same
        // whatever was read before it.
        self.uniq = 0;
        self.matchSeq = 0;
        self.forSeq = 0;
        self.declName = NO_SYM;
        self.usesAbandoned = false;
        // `@init`, `@fini`, `@panic` before a function: what the program's startup, shutdown
        // and a failed `assert!` run (`parseAttrs`, held to the function by `applyAttrs`).
        attrs: long = self.parseAttrs();
        self.vis = self.parseVisibility();
        // `builtin name params -> T;`: the compiler provides the body.
        if (self.word("builtin") && !self.namedHere() && self.peekNext().kind == Tok.Id) {
            self.advance();
            self.fnAttrs = FN_BUILTIN_DECL;
        }
        if (attrs != 0) {
            st: long = self.parseStatement();
            self.applyAttrs(st, attrs);
            self.notePage(st, self.curMod, false);
            for k in 0..self.pending.len() { self.notePage(self.pending.get(k), self.curMod, false); }
            self.pending.clear();
            return;
        }
        // `var NAME: T = value;` declares a global that may be written, and may initialize
        // at startup. Without it a global is a constant the compiler computes. Read here, in
        // the same slot as the visibility, and consumed by `parseGlobal`.
        if (self.word("var") && !self.namedHere()) { self.advance(); self.varDecl = true; }
        // `macro name params -> T { }`: a function the compiler runs, called as `name!(...)`.
        // Its name is registered now, so a call parses as one; the declaration itself is
        // read at the end of the page, when every module's types are known (`MacroSnap`).
        if (self.word("macro") && !self.namedHere()) {
            self.advance();
            mname: Token = self.expect(Tok.Id);
            regNoteMacro(self.qualify(nameOf(mname.text)));
            self.pendingMacros.push(MacroSnap { name: mname.text, pos: self.lx.pos, line: self.lx.fileLine,
                                                col: self.lx.charNumber, file: self.lx.currentFile,
                                                pkg: self.lx.currentPackage, cur: self.cur,
                                                peeked: self.peeked, hasPeeked: self.hasPeeked, vis: self.vis,
                                                curPos: self.curPos, peekPos: self.peekPos,
                                                src: self.lx.src, mod: self.curMod, loaded: -1 });
            self.skipMacroDecl();
            return;
        }
        self.notePage(self.parseStatement(), self.curMod, false);
        if (self.varDecl) { self.err(stringOf("`var` applies only to a global declaration\nhelp: write `var NAME: T = value;`")); }
        if (self.fnAttrs != 0) { self.err(stringOf("`builtin` applies only to a function declaration\nhelp: write `builtin name params -> T;`")); }
        for k in 0..self.pending.len() { self.notePage(self.pending.get(k), self.curMod, false); }
        self.pending.clear();
    }

    // A declaration read under a `recover`. An error in it is reported where it was found and
    // raises here (`failAt`, `fail`); the declaration is then taken back out of every table it
    // had reached (`rewindTo`), the rest of its text is skipped (`skipToNextDecl`), and the
    // module goes on with the next one, so one run reports an error in each declaration that has
    // one. The compile stops once the whole page is read (`stopIfErrors` in the driver), so no
    // later phase sees a program with a declaration missing.
    //
    // The raise and this `recover` are one subsystem: every frame between them is the parser's or
    // the lexer's, none holds a lock, and what they leave half built is this declaration's, which
    // the rewind takes back. Their own locals leak, which only an error pays for.
    parseDeclRecovering &self -> void {
        m: ParseMark = self.markHere();
        failed: bool = false;
        unsafe {
            recover { self.parseDecl(); } else { failed = true; }
        }
        if (failed) {
            self.rewindTo(m);
            self.skipToNextDecl(m.startPos);
        }
    }

    markHere &self -> ParseMark {
        file: str = nameOf(self.lx.currentFile);
        seq: long = -1;
        had: Option<long> = self.closureSeq.find(file);
        match had { Some(n) { seq = n; } None { } }
        return ParseMark { ast: self.ast.mark(), reg: gReg.mark(), ops: opsMark(), startPos: self.curPos,
                           gPos: gPos, pendingMacros: self.pendingMacros.len(),
                           tplBounds: self.tplBounds.len(), scopes: self.scopes.len(),
                           scopeStart: self.scopeStart.len(), implChecks: self.implChecks.len(),
                           pendingInits: self.pendingInits.len(), closureBound: self.closureBound.len(),
                           closureName: self.closureName.len(), captures: self.captures.len(),
                           closureFile: file, closureSeq: seq, fnReturnsAdded: self.fnReturnsAdded.len(),
                           pending: self.pending.len(), typeVars: self.typeVars.len(),
                           lenVars: self.lenVars.len(), tplParams: self.tplParams.len(),
                           selfParams: self.selfParams.len(), selfInfo: self.selfInfo.len(),
                           pageIds: self.pageIds.len(), tryHole: self.tryHole.len(),
                           toOrder: self.toOrder.len(), contPre: self.contPre.len(),
                           inImpl: self.inImpl, uniq: self.uniq, matchSeq: self.matchSeq,
                           forSeq: self.forSeq, loopDepth: self.loopDepth, fnDepth: self.fnDepth,
                           implMangled: self.implMangled, noCast: self.noCast, inPointee: self.inPointee,
                           quoteDepth: self.quoteDepth, unsafeDepth: self.unsafeDepth, vis: self.vis,
                           varDecl: self.varDecl, boundFirst: self.boundFirst, boundCount: self.boundCount,
                           selfTpl: self.selfTpl, lenArgOk: self.lenArgOk, typeVarUses: self.typeVarUses,
                           plainBody: self.plainBody, blanketVar: self.blanketVar, blanketAs: self.blanketAs,
                           retTy: self.retTy, retOk: self.retOk, toMark: self.toMark, toImpure: self.toImpure,
                           toCond: self.toCond, toLhs: self.toLhs, contIf: self.contIf,
                           retNever: self.retNever, fnAttrs: self.fnAttrs, lastStmt: self.lastStmt };
    }

    // Everything a declaration added, taken back, and the state it began in put back. The lexer
    // is not: the skip goes on from where the error left it.
    rewindTo &self m:ParseMark -> void {
        // Cut short while reading compiler-written text: the module's own cursor comes back.
        if (self.synthSaved.len() > 0) {
            c: Cursor = self.synthSaved.get(0);
            self.lx = c.lx;
            self.cur = c.cur;
            self.peeked = c.peeked;
            self.hasPeeked = c.hasPeeked;
            self.curPos = c.curPos;
            self.peekPos = c.peekPos;
            self.synthSaved.clear();
        }
        self.ast.rewindTo(m.ast);
        gReg.rewindTo(m.reg);
        opsRewind(m.ops);
        for k in m.fnReturnsAdded..self.fnReturnsAdded.len() { self.fnReturns.remove(nameOf(self.fnReturnsAdded.get(k))); }
        self.fnReturnsAdded.truncate(m.fnReturnsAdded);
        if (m.closureSeq < 0) { self.closureSeq.remove(m.closureFile); } else { self.closureSeq.put(m.closureFile, m.closureSeq); }
        self.pendingMacros.truncate(m.pendingMacros);
        self.tplBounds.truncate(m.tplBounds);
        self.scopes.truncate(m.scopes);
        self.scopeStart.truncate(m.scopeStart);
        self.implChecks.truncate(m.implChecks);
        self.pendingInits.truncate(m.pendingInits);
        self.closureBound.truncate(m.closureBound);
        self.closureName.truncate(m.closureName);
        self.captures.truncate(m.captures);
        self.pending.truncate(m.pending);
        self.typeVars.truncate(m.typeVars);
        self.lenVars.truncate(m.lenVars);
        self.tplParams.truncate(m.tplParams);
        self.selfParams.truncate(m.selfParams);
        self.selfInfo.truncate(m.selfInfo);
        self.pageIds.truncate(m.pageIds);
        self.pageMod.truncate(m.pageIds);
        self.pageDeferred.truncate(m.pageIds);
        self.tryHole.truncate(m.tryHole);
        self.tryOperand.truncate(m.tryHole);
        self.tryName.truncate(m.tryHole);
        self.toOrder.truncate(m.toOrder);
        self.contPre.truncate(m.contPre);
        self.inImpl = m.inImpl;
        self.uniq = m.uniq;
        self.matchSeq = m.matchSeq;
        self.forSeq = m.forSeq;
        self.loopDepth = m.loopDepth;
        self.fnDepth = m.fnDepth;
        self.implMangled = m.implMangled;
        self.noCast = m.noCast;
        self.inPointee = m.inPointee;
        self.quoteDepth = m.quoteDepth;
        self.unsafeDepth = m.unsafeDepth;
        self.vis = m.vis;
        self.varDecl = m.varDecl;
        self.boundFirst = m.boundFirst;
        self.boundCount = m.boundCount;
        self.selfTpl = m.selfTpl;
        self.lenArgOk = m.lenArgOk;
        self.typeVarUses = m.typeVarUses;
        self.plainBody = m.plainBody;
        self.blanketVar = m.blanketVar;
        self.blanketAs = m.blanketAs;
        self.retTy = m.retTy;
        self.retOk = m.retOk;
        self.toMark = m.toMark;
        self.toImpure = m.toImpure;
        self.toCond = m.toCond;
        self.toLhs = m.toLhs;
        self.contIf = m.contIf;
        self.retNever = m.retNever;
        self.fnAttrs = m.fnAttrs;
        self.lastStmt = m.lastStmt;
        gPos = m.gPos;
        if (self.declName != NO_SYM) { self.abandoned.push(self.declName); }
        self.declName = NO_SYM;
        self.usesAbandoned = false;
    }

    // Past the rest of a declaration an error cut short, to the next token that can begin one:
    // an identifier or an `@` in the first column of its line, which is where a top-level
    // declaration is written and where nothing inside one is. Braces are not counted: a missing
    // `}` is as likely an error as any, and a count from a declaration that lost one would swallow
    // the rest of the file. The token the declaration began with never qualifies, so the skip
    // always moves. Nothing on the way is reported: a lexer error met there raises quietly
    // (`gQuiet`), and the skip goes on from past it.
    skipToNextDecl &self startPos:long -> void {
        gQuiet = gQuiet + 1;
        going: bool = true;
        while (going) {
            unsafe {
                recover {
                    while (!self.check(Tok.FileEnd) && !(self.curPos != startPos && self.atDeclStart())) { self.advance(); }
                    going = false;
                } else { }
            }
        }
        gQuiet = gQuiet - 1;
    }
    atDeclStart &self -> bool {
        return (self.check(Tok.Id) || self.check(Tok.AtSign)) && posCol(self.curPos) == 1;
    }

    // Whether `n` is the type a declaration taken back was declaring. Its error has been reported;
    // a use of the name is not reported again as missing.
    abandonedName &self n:Sym -> bool {
        if (self.abandoned.len() == 0) { return false; }
        bare: str = lastComponentOf(nameOf(n));
        for k in 0..self.abandoned.len() {
            if (nameOf(self.abandoned.get(k)) == bare) { return true; }
        }
        return false;
    }

    // `@init @fini @panic @recover`, each at most once, before a top-level function.
    parseAttrs &self -> long {
        attrs: long = 0;
        while (self.check(Tok.AtSign)) {
            self.advance();
            w: Token = self.expect(Tok.Id);
            n: str = nameOf(w.text);
            bit: long = 0;
            if (n == "init") { bit = FN_INIT; }
            else if (n == "fini") { bit = FN_FINI; }
            else if (n == "panic") { bit = FN_PANIC; }
            else if (n == "recover") { bit = FN_RECOVER; }
            else { self.err(format("unknown attribute `@{}`\nnote: a function may be marked `@init`, `@fini`, `@panic` or `@recover`", n)); }
            if ((attrs & bit) != 0) { self.err(format("duplicate attribute `@{}`", n)); }
            attrs = attrs | bit;
        }
        return attrs;
    }
    // Held to its shape here, where the declaration is: a hook is `name -> void` with a body,
    // run with nothing to hand it; the `@panic` function takes the message and does not come back.
    applyAttrs &self st:long attrs:long -> void {
        s: Stmt = self.ast.stmts.get(st);
        if (s.kind != StmtKind.FunctionDef) {
            self.err(stringOf("an attribute (`@init`, `@fini`, `@panic` or `@recover`) can only mark a function definition"));
        }
        f: FnNode = self.ast.fns.get(s.at);
        n: str = lastComponentOf(nameOf(f.name));
        if ((attrs & (FN_INIT | FN_FINI)) != 0) {
            if (f.argCount != 0 || f.returnKind != Lit.Void || isNeverFn(f) || f.body < 0 || f.isTemplate) {
                self.err(format("wrong signature for startup or shutdown hook `{}`\nnote: a hook takes no parameters, returns nothing, has a body and is not generic\nhelp: declare it as `{} -> void {{ ... }}`", n, n));
            }
            if ((attrs & FN_INIT) != 0 && (attrs & FN_FINI) != 0) { self.err(format("`{}` cannot be both `@init` and `@fini`", n)); }
        }
        if ((attrs & FN_PANIC) != 0) {
            ok: bool = f.argCount == 1 && isNeverFn(f) && !f.isTemplate;
            if (ok) {
                p: VarDeclNode = self.ast.paramAt(f, 0);
                ok = p.kind == Lit.Str && !p.isVariadic;
            }
            if (!ok) { self.err(format("wrong signature for the `@panic` function `{}`\nhelp: declare it as `{} msg:str -> never`", n, n)); }
        }
        // The `@recover` function links a record and answers the one it replaced. Code the
        // compiler writes calls it, so its shape is fixed.
        if ((attrs & FN_RECOVER) != 0) {
            ok: bool = f.argCount == 1 && f.returnKind == Lit.Long && !isNeverFn(f) && !f.isTemplate && f.body >= 0;
            if (ok) {
                p: VarDeclNode = self.ast.paramAt(f, 0);
                ok = p.kind == Lit.Long && !p.isVariadic;
            }
            if (!ok) { self.err(format("wrong signature for the `@recover` function `{}`\nhelp: declare it as `{} rec:long -> long {{ ... }}`", n, n)); }
        }
        f.attrs = f.attrs | attrs;
        self.ast.fns.set(s.at, f);
    }

    notePage &self st:long mod:long deferred:bool -> void {
        self.pageIds.push(st);
        self.pageMod.push(mod);
        self.pageDeferred.push(deferred);
    }

    // A macro a `.klib` brought, already parsed: it goes on the page where the parser would have
    // put it, after every module, in the order its declaration was met.
    noteLoadedMacro &self st:long mod:long -> void {
        t: Token = tokenOf(Tok.FileEnd);
        self.pendingMacros.push(MacroSnap { name: NO_SYM, pos: 0, line: 0, col: 0, file: NO_SYM, pkg: NO_SYM,
                                            cur: t, peeked: t, hasPeeked: false, vis: Vis.Local, curPos: 0, peekPos: 0,
                                            src: "", mod: mod, loaded: st });
    }

    finishPage &self -> long {
        self.parseDeferredMacros();
        opsEnd();
        gReg.journal = false;
        return self.ast.addBlock(self.pageIds);
    }

    // Past a macro's signature and body: the first `{` opens the body, and its match closes it.
    skipMacroDecl &self -> void {
        depth: long = 0;
        while (true) {
            if (self.check(Tok.FileEnd)) { self.err(stringOf("unexpected end of file in a macro declaration\nnote: a macro needs a body")); }
            if (self.check(Tok.LeftCurly)) { depth = depth + 1; }
            if (self.check(Tok.RightCurly)) {
                depth = depth - 1;
                if (depth == 0) { self.advance(); return; }
            }
            self.advance();
        }
    }
    // Every macro met on the page, read now from where it was met. The lexer is put back on its
    // module's text at that spot, so every position is the declaration's own.
    parseDeferredMacros &self -> void {
        for k in 0..self.pendingMacros.len() {
            m: MacroSnap = self.pendingMacros.get(k);
            if (m.loaded >= 0) { self.notePage(m.loaded, m.mod, true); continue; }
            self.lx = lexerOf(m.src);
            self.lx.pos = m.pos; self.lx.fileLine = m.line; self.lx.charNumber = m.col;
            self.lx.currentFile = m.file; self.lx.currentPackage = m.pkg;
            self.cur = m.cur; self.peeked = m.peeked; self.hasPeeked = m.hasPeeked;
            self.curPos = m.curPos; self.peekPos = m.peekPos;
            self.vis = m.vis;
            self.varDecl = false;
            self.uniq = 0;
            self.matchSeq = 0;
            self.forSeq = 0;
            self.curMod = m.mod;
            opsModule(m.mod);
            gPos = m.curPos;
            if (canRecover()) { self.deferredMacroRecovering(m); } else { self.deferredMacro(m); }
        }
        gPos = 0;
        self.pendingMacros.clear();
    }
    // One of them under a `recover`, as a declaration is (`parseDeclRecovering`). The next one is
    // read from its own place, so nothing needs skipping.
    deferredMacroRecovering &self m:MacroSnap -> void {
        mk: ParseMark = self.markHere();
        failed: bool = false;
        unsafe {
            recover { self.deferredMacro(m); } else { failed = true; }
        }
        if (failed) { self.rewindTo(mk); }
    }
    deferredMacro &self m:MacroSnap -> void {
        self.declName = NO_SYM;
        self.usesAbandoned = false;
        fst: long = self.parseFunctionDef(m.name);
        self.ast.stmtPos.set(fst, m.curPos);
        // A macro is a function the compiler runs while checking. Its body has to be here to be
        // run; a symbol in another object is of no use to the evaluator.
        if (self.ast.fns.get(self.ast.stmts.get(fst).at).body < 0) {
            self.err(format("macro `{}` has no body\nnote: the compiler runs a macro while it checks, so its body has to be here, not in another object",
                            nameOf(m.name)));
        }
        self.notePage(fst, m.mod, true);
    }
}

methods Parser {
    // ─── declarations ────────────────────────────────────────────────────────

    // `struct Name { f: T, g: [T; N], p: *T }`. The layout is computed here and registered; the
    // statement left behind is only a marker, so the top-level list stays uniform.
    parseStructDecl &self -> long {
        name: Token = self.expect(Tok.Id);
        self.declName = name.text;
        if (self.check(Tok.LessThan)) { return self.parseGenericStruct(name.text); }
        self.requireTypeNameFree(nameOf(name.text));
        q: Sym = self.qualify(nameOf(name.text));
        self.expect(Tok.LeftCurly);
        // Registered now, so the body can name the type it is declaring behind an indirection
        // (`kids: Box<Tree>`, `next: *Tree`); sized for real at the `}`.
        at: long = regBeginStruct(q, self.lx.currentPackage);

        fields: Vec<FieldDef>;
        cursor: long = 0;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            fname: Token = self.expect(Tok.Id);
            self.rejectDuplicateField(fields, fname.text, q);
            self.expect(Tok.Colon);

            if (self.check(Tok.LeftSquare)) {                 // an inline array field
                self.advance();
                elem: TypeRef = self.parseTypeRef();
                self.expect(Tok.Semicolon);
                n: long = self.parseArrayLength();
                self.expect(Tok.RightSquare);
                want: FieldDef = FieldDef { name: fname.text, kind: elem.base,
                                            structName: elem.name, offset: 0,
                                            isArray: true, count: n };
                p: Placed = placeField(cursor, want);
                fields.push(p.field);
                cursor = p.next;
            } else {
                t: TypeRef = self.parseTypeRef();
                if (t.base == Lit.Void) {
                    self.err(format("struct field `{}` cannot be `void`", nameOf(fname.text)));
                }
                want: FieldDef = FieldDef { name: fname.text, kind: t.base, structName: t.name,
                                            offset: 0, isArray: false, count: 0 };
                p: Placed = placeField(cursor, want);
                fields.push(p.field);
                cursor = p.next;
            }
            self.eat(Tok.Comma);                              // optional separator
        }
        self.expect(Tok.RightCurly);

        regFinishStruct(at, fields, alignUp(cursor, 8), false);
        self.ast.structDecls.push(q);
        st: long = self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1);
        return st;
    }

    rejectDuplicateField &self fields:Vec<FieldDef> name:Sym owner:Sym -> void {
        for i in 0..fields.len() {
            if (fields.get(i).name == name) {
                self.err(format("duplicate field `{}` in struct `{}`",
                                nameOf(name), nameOf(owner)));
            }
        }
    }

    // Is `q` a generic sum type, a template declared with `enum`?
    isGenericSum &self q:str -> bool {
        at: long = gReg.findTemplate(q);
        if (at < 0) { return false; }
        return gReg.templateDef(at).isEnum;
    }

    // Does the sum type (declared, or a template) have a variant of this name?
    sumHasVariant &self owner:Sym variant:Sym -> bool {
        at: long = gReg.findEnumSym(owner);
        if (at >= 0) { return gReg.findVariant(gReg.enumDef(at), nameOf(variant)) >= 0; }
        tat: long = gReg.findTemplateSym(owner);
        if (tat < 0) { return false; }
        return gReg.findGVariant(gReg.templateDef(tat), nameOf(variant)) >= 0;
    }

    // `E.V` or `E.V(a, b)` as the tagged union it is: `{ $tag: <n>, $V$0: a, $V$1: b }`. The
    // payload fields are named after the variant, so two variants never share a field and the
    // layout can overlap them safely.
    parseVariant &self owner:Sym variant:Sym -> NodeId {
        tag: long = 0;
        arity: long = 0;
        backing: Lit = Lit.Int;              // what a generic sum type's tag is stamped as
        at: long = gReg.findEnumSym(owner);
        if (at >= 0) {
            d: EnumDef = gReg.enumDef(at);
            backing = d.backing;
            vi: long = gReg.findVariant(d, nameOf(variant));
            if (vi < 0) { self.err(format("no variant `{}` in enum `{}`", nameOf(variant), nameOf(owner))); }
            vd: VariantDef = gReg.variantAt(d, vi);
            tag = vd.value;
            arity = vd.payloadCount;
        } else {
            // A generic sum type. Its variants are known from the template; which instance this
            // is, is not: the checker settles that from the type the value is being used as.
            t: GTemplate = gReg.templateDef(gReg.findTemplateSym(owner));
            vi: long = gReg.findGVariant(t, nameOf(variant));
            if (vi < 0) { self.err(format("no variant `{}` in enum `{}`", nameOf(variant), nameOf(owner))); }
            gv: GVariant = gReg.gVariantAt(t, vi);
            tag = gv.value;
            arity = gv.payloadCount;
        }

        args: Vec<NodeId>;
        // Read against the arity as it goes, so running out is reported where the value should
        // have been. Comparing counts after the whole list would say the same thing one token
        // late, pointing at the `)` rather than at what was missing.
        if (arity == 0) {
            if (self.check(Tok.LeftParen)) {
                self.err(format("variant `{}` carries no payload", nameOf(variant)));
            }
        } else {
            if (!self.check(Tok.LeftParen)) {
                self.err(format("variant `{}` carries {}\nhelp: write `{}(...)`",
                                nameOf(variant), plural(arity, "value"), nameOf(variant)));
            }
            self.advance();
            for a in 0..arity {
                if (self.check(Tok.RightParen)) {
                    self.err(format("too few values for variant `{}`: expected {}, found {}",
                                    nameOf(variant), arity, a));
                }
                if (a > 0) { self.expect(Tok.Comma); }
                args.push(self.parseExpr());
            }
            if (!self.check(Tok.RightParen)) {
                self.err(format("variant `{}` carries only {}", nameOf(variant), plural(arity, "value")));
            }
            self.expect(Tok.RightParen);
        }

        inits: Vec<InitNode>;
        inits.push(InitNode { name: intern(enumTagField()),
                              value: self.ast.leaf(Op.Literal, Payload.Num(tag), backing) });
        for k in 0..args.len() {
            inits.push(InitNode { name: enumPayloadField(nameOf(variant), k), value: args.get(k) });
        }
        first: long = self.ast.inits.len();
        self.ast.inits.extend(inits);
        self.ast.lits.push(LitNode { typeName: owner, firstInit: first, initCount: inits.len(),
                                     rest: NO_NODE });
        return self.ast.leafOf(Op.StructLit, Payload.Lit(self.ast.lits.len() - 1),
                               Lit.Struct, owner);
    }

    // `E.V` where E carries no payloads: the variant's value, at the enum's backing width. The
    // literal carries E as its companion name, which nothing that types an integer reads; a
    // `...any` run does, to box `println("{}", E.V)` through E's `Display` (`Checker.checkAnyArg`).
    enumConst &self owner:Sym variant:Sym -> NodeId {
        d: EnumDef = gReg.enumDef(gReg.findEnumSym(owner));
        vi: long = gReg.findVariant(d, nameOf(variant));
        if (vi < 0) {
            self.err(format("no variant `{}` in enum `{}`", nameOf(variant), nameOf(owner)));
        }
        return self.ast.leafOf(Op.Literal, Payload.Num(gReg.variantAt(d, vi).value), d.backing, owner);
    }

    // An integer constant as an expression, for the tag a variant constructor writes.
    numberNode &self v:long -> NodeId {
        return self.ast.leaf(Op.Literal, Payload.Num(v), Lit.Long);
    }

    // `Name { f: v, g: w }`, a struct literal. The name is already consumed.
    parseStructLit &self typeName:Sym -> NodeId {
        self.expect(Tok.LeftCurly);
        inits: Vec<InitNode>;
        rest: NodeId = NO_NODE;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            // `..rest`: every field not named here comes from another value of this type. It
            // ends the literal: what followed it would have nothing left to say.
            if (self.check(Tok.DotDot)) {
                self.advance();
                rest = self.parseExpr();
                self.eat(Tok.Comma);
                if (!self.check(Tok.RightCurly)) {
                    self.err(stringOf("nothing can follow `..` in a struct literal\nnote: `..` takes all the remaining fields"));
                }
                break;
            }
            fname: Token = self.expect(Tok.Id);
            self.expect(Tok.Colon);
            inits.push(InitNode { name: fname.text, value: self.parseExpr() });
            self.eat(Tok.Comma);
        }
        self.expect(Tok.RightCurly);
        first: long = self.ast.addInits(inits);
        self.ast.lits.push(LitNode { typeName: typeName, firstInit: first,
                                     initCount: inits.len(), rest: rest });
        id: long = self.ast.lits.len() - 1;
        v: NodeId = self.ast.leaf(Op.StructLit, Payload.Lit(id), Lit.Struct);
        e: Expr = self.ast.expr(v);
        self.ast.setExpr(v, Expr { op: e.op, left: e.left, right: e.right, kind: Lit.Struct,
                                   structName: typeName, isParen: false, payload: e.payload });
        return v;
    }

    // `name.method()` with no arguments, over a receiver that is an already-resolved local. The
    // desugared `for` reads its iterator twice a turn and each read needs a node of its own.
    methodCallOn &self name:Sym k:Lit sname:Sym method:str -> NodeId {
        recv: NodeId = self.nameRef(name, k, sname);
        none: Vec<NodeId>;
        self.ast.calls.push(CallNode { name: intern(method), receiver: recv,
                                       firstArg: self.ast.addArgs(none), argCount: 0,
                                       slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        return self.ast.leaf(Op.MethodCall, Payload.Call(self.ast.calls.len() - 1), Lit.Void);
    }

    // `for name in iterable { }`: a `while` with a step, which is why it is not desugared into a
    // plain while: `continue` has to run the step, and a bare while with the increment last would
    // skip it and spin forever.
    parseFor &self -> long {
        self.pushScope();
        it: Token = self.expect(Tok.Id);
        itKind: Lit = Lit.Long;
        itStruct: Sym = NO_SYM;
        overIter: bool = false;
        // The element's type is written out, and writing it is what says this walks an iterator
        // rather than a range: a range counts with a `long` and never names a type.
        if (self.eat(Tok.Colon)) {                 // `for x: T in it`, walking an iterator
            t: TypeRef = self.parseTypeRef();
            itKind = t.base;
            itStruct = t.name;
            overIter = true;
        }
        if (!self.eatWord("in")) { self.err(format("expected `in`, found {}", describeTok(self.cur))); }

        // `for x: T in it { body }` is the `while (it.hasNext())` loop you would have written by
        // hand (`iterLoop` builds it).
        if (overIter) {
            // The iterator is read twice a turn (`hasNext`, then `next`) so it has to be a
            // place, not an expression re-evaluated each turn: that would build it again rather
            // than advance it, and the loop would never end. A named variable is used as it is,
            // so the concrete case inlines exactly as before. Anything else is bound first, to a
            // hidden local typed `Iter<T>`: T is already written in the header, and any iterator
            // coerces to the trait object. The cost is a dispatch per call where a named concrete
            // iterator would have inlined: exactly the cost of writing `it: Iter<T> = mk();` by
            // hand, which is what this is.
            srcName: Sym = NO_SYM;
            srcKind: Lit = Lit.Long;
            srcStruct: Sym = NO_SYM;
            bindDecl: long = NO_STMT;
            bindAsn: long = NO_STMT;
            if (self.check(Tok.Id) && self.peekNext().kind == Tok.LeftCurly) {
                src: Token = self.advance();
                b: Binding = self.bindingOf(src.text);
                if (b.renamed == NO_SYM) {
                    self.err(format("`{}` is not a local variable", nameOf(src.text)));
                }
                srcName = b.renamed; srcKind = b.kind; srcStruct = b.structName;
            } else {
                srcExpr: NodeId = self.parseExpr();
                ti: long = gReg.findTrait("Iter");
                if (ti < 0) {
                    self.err(stringOf("`for x: T in <expr>` needs the trait `Iter<T>`\nhelp: the standard library has it in `stdlib::iter`: `#include <stdlib::iter>`"));
                }
                targs: Vec<TypeRef>;
                targs.push(TypeRef { base: itKind, name: itStruct });
                srcKind = Lit.TraitObj;
                srcStruct = regStampTrait(intern("Iter"), targs);
                // Held per loop rather than in a member: the body may hold another `for`, and one
                // shared binding would hand the outer loop's iterator to the inner one. The name
                // collides with an enclosing loop's on purpose: `declareLocal` renames it, which
                // is the same shadowing every other nested local gets.
                srcName = self.declareLocal(intern("$for"), srcKind, srcStruct);
                self.ast.decls.push(VarDeclNode { name: srcName, kind: srcKind,
                                                  structName: srcStruct,
                                                  isArray: false, count: 0, conv: Conv.None,
                                                  isVariadic: false, elemKind: Lit.Void,
                                                  elemStruct: NO_SYM, init: NO_NODE });
                bindDecl = self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1);
                itLhs: NodeId = self.nameRef(srcName, srcKind, srcStruct);
                itAsn: NodeId = self.ast.binary(Op.Assignment, itLhs, srcExpr, srcKind);
                self.ast.exprStmts.push(ExprStmtNode { value: itAsn });
                bindAsn = self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1);
            }

            return self.iterLoop(it, itKind, itStruct, srcName, srcKind, srcStruct, bindDecl, bindAsn);
        }

        // `for x in &xs`: the loop lends `xs`, and `x` is a borrow of each element that may be
        // written through. Only a collection is lent this way; a range has nothing to lend.
        lend: bool = self.eat(Tok.Ampersand);
        seq: NodeId = self.parseExpr();
        upper: NodeId = NO_NODE;
        if (!lend && self.eat(Tok.DotDot)) { upper = self.parseExpr(); }
        // No `..` and no type: a collection, or an iterator held in a variable, walked by what
        // its type says it is.
        if (upper == NO_NODE) { return self.parseForEach(it, lend, seq); }

        renamed: Sym = self.declareLocal(it.text, itKind, itStruct);
        self.ast.decls.push(VarDeclNode { name: renamed, kind: itKind, structName: itStruct,
                                          isArray: false, count: 0, conv: Conv.None,
                                          isVariadic: false, elemKind: Lit.Void,
                                          elemStruct: NO_SYM, init: seq });
        declStmt: long = self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1);

        self.loopDepth = self.loopDepth + 1;
        body: long = self.parseBlock();
        self.loopDepth = self.loopDepth - 1;
        self.popScope();

        // A range loop is the variable set to the lower bound, a test against the upper one, and
        // an increment as the loop's step. It stays a step rather than the body's last statement
        // because `continue` has to run it: otherwise the loop spins forever.
        cond: NodeId = upper;
        step: long = -1;
        if (upper != NO_NODE) {
            cond = self.ast.binary(Op.LessThan, self.nameRef(renamed, itKind, itStruct),
                                   upper, Lit.Bool);
            one: NodeId = self.numberLit(1, Lit.Long);
            inc: NodeId = self.ast.binary(Op.Addition,
                                          self.nameRef(renamed, itKind, itStruct), one, itKind);
            asn: NodeId = self.ast.binary(Op.Assignment,
                                          self.nameRef(renamed, itKind, itStruct), inc, itKind);
            self.ast.exprStmts.push(ExprStmtNode { value: asn });
            stepStmt: long = self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1);
            stepIds: Vec<long>;
            stepIds.push(stepStmt);
            step = self.ast.addBlock(stepIds);
        }

        self.ast.whiles.push(WhileNode { cond: cond, body: body, step: step });
        loopStmt: long = self.ast.addStmt(StmtKind.While, self.ast.whiles.len() - 1);

        // The declaration and the loop are two statements, wrapped in one block so the loop
        // variable's scope is exactly the loop.
        ids: Vec<long>;
        ids.push(declStmt);
        ids.push(loopStmt);
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(ids) });
        return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
    }

    // `for x: T in it { body }` is exactly the loop you would have written by hand:
    //
    //     while (it.hasNext()) { x: T = it.next(); body }
    //
    // and nothing more. There is no step: an iterator advances itself inside `next()`, so a
    // `continue` re-tests `hasNext` and is already right. `bindDecl`/`bindAsn` bind an iterator
    // that is not a named variable to a hidden one first (NO_STMT when it is one).
    iterLoop &self it:Token itKind:Lit itStruct:Sym srcName:Sym srcKind:Lit srcStruct:Sym bindDecl:long bindAsn:long -> long {
        renamed: Sym = self.declareLocal(it.text, itKind, itStruct);
        self.ast.decls.push(VarDeclNode { name: renamed, kind: itKind, structName: itStruct,
                                          isArray: false, count: 0, conv: Conv.None,
                                          isVariadic: false, elemKind: Lit.Void,
                                          elemStruct: NO_SYM, init: NO_NODE });
        declStmt: long = self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1);

        lhs: NodeId = self.nameRef(renamed, itKind, itStruct);
        nxt: NodeId = self.methodCallOn(srcName, srcKind, srcStruct, "next");
        asn: NodeId = self.ast.binary(Op.Assignment, lhs, nxt, itKind);
        self.ast.exprStmts.push(ExprStmtNode { value: asn });
        headStmt: long = self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1);

        self.loopDepth = self.loopDepth + 1;
        ibody: long = self.parseBlock();
        self.loopDepth = self.loopDepth - 1;
        self.popScope();

        // The fetch goes at the head of the body, ahead of what was written in it.
        inner: Vec<long>;
        inner.push(headStmt);
        n: long = self.ast.blockLen(ibody);
        for j in 0..n { inner.push(self.ast.stmtIdAt(ibody, j)); }
        ifull: long = self.ast.addBlock(inner);

        icond: NodeId = self.methodCallOn(srcName, srcKind, srcStruct, "hasNext");
        self.ast.whiles.push(WhileNode { cond: icond, body: ifull, step: -1 });
        iloop: long = self.ast.addStmt(StmtKind.While, self.ast.whiles.len() - 1);

        // The hidden iterator lives exactly as long as the loop: both go in one block, so
        // it is released where the loop ends rather than at the end of the enclosing scope.
        iids: Vec<long>;
        if (bindDecl != NO_STMT) { iids.push(bindDecl); iids.push(bindAsn); }
        iids.push(declStmt);
        iids.push(iloop);
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(iids) });
        return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
    }

    // `for x in xs { body }` over a `Vec<T>`, a slice `[T]` or an array `[T; N]`: an index loop
    // over the elements where they lie, with no iterator object and nothing allocated.
    //
    //     { $forpK: *T; $fornK: long; $foriK: long;
    //       unsafe { $forpK = <xs's first element>; $fornK = <xs's length>; }
    //       $foriK = 0;
    //       while ($foriK < $fornK) step { $foriK = $foriK + 1; } {
    //           x: T; x = $forpK[$foriK];
    //           body
    //       } }
    //
    // The base and the length are read once, which is sound because the body may not change
    // `xs` while it is being walked: the immutability guard holds the loop to that, with every
    // callee's write mask in hand (`ConstGuard.holdLoop`). `x` is written here as a copy of the
    // element; once types are concrete, an element that is a struct becomes a borrow of it where
    // it lies (`Checker.bmForLoop`), so nothing is copied or moved out of the collection.
    //
    // `for x in &xs` lends `xs` to the loop (`&xs` is the setup's first statement, which is what
    // convention inference and the guard read as a write) and is `$forwK` rather than `$forpK`:
    // the guard lets the body write through `x`, which the plain form refuses.
    //
    // A variable that holds an iterator is walked by its `hasNext`/`next`, its element type read
    // from its `Iter<T>` implementation: `for x in it` is `for x: T in it`.
    parseForEach &self it:Token lend:bool src:NodeId -> long {
        pt: PlaceTy = self.placeTy(src);
        if (!pt.ok) {
            self.err(stringOf("cannot tell what this `for x in ...` walks\nnote: `for x in xs` walks a variable or a field of one, whose type says what it holds\nhelp: bind the value to a local first, or write the element type: `for x: T in it`"));
        }
        shape: long = FOR_NONE;
        elem: TypeRef = typeRefOf(Lit.Void);
        if (pt.isArray) { shape = FOR_ARRAY; elem = TypeRef { base: pt.kind, name: pt.name }; }
        else if (pt.kind == Lit.Slice) {
            shape = FOR_SLICE;
            elem = unmangledType(nameOf(pt.name));
            // `[T]` records its element as the spelling `T`, which reads back as a struct of that
            // name: inside a generic body it is the type parameter, substituted per instance.
            if (elem.base == Lit.Struct && self.isTypeVar(elem.name)) { elem.base = Lit.TypeVar; }
        } else if (pt.kind == Lit.Struct || pt.kind == Lit.Ref) {
            // A type that views its elements as a slice (`AsSlice<T>`, a core trait): walked as
            // the slice its `asSlice` hands back. What `Vec` is walked by.
            elem = self.traitElemOf(pt.name, "AsSlice");
            if (elem.base != Lit.Void) { shape = FOR_VIEW; }
            else {
                elem = self.iterElemOf(pt.name);
                if (elem.base != Lit.Void) { shape = FOR_ITER; }
            }
        }
        if (shape == FOR_NONE) {
            // An instance of a template nothing declares yet (`Vec<long>` in a file that does not
            // include `stdlib::vec`): the type is what is wrong, as `match` says.
            if (pt.name != NO_SYM) {
                ri: long = gReg.findRequestSym(pt.name);
                if (ri >= 0 && gReg.findTemplateSym(gReg.requestAt(ri).base) < 0) {
                    tb: str = lastComponentOf(nameOf(gReg.requestAt(ri).base));
                    self.err(format("cannot find type `{}` in this scope{}", tb, stdlibHint(tb)));
                }
            }
            self.err(format("cannot walk a `{}` with `for x in`\nnote: `for x in` walks a slice, an array, a type implementing `AsSlice` (such as `Vec`), or a variable holding an iterator",
                            typeMangleName(pt.kind, pt.name)));
        }
        if (shape == FOR_ITER) {
            if (lend) {
                self.err(stringOf("cannot lend an iterator with `for x in &it`\nnote: an iterator is walked by its own `hasNext` and `next`, and has nothing to lend\nhelp: drop the `&`"));
            }
            srcName: Sym = NO_SYM;
            se: Expr = self.ast.expr(src);
            if (se.op == Op.Lvalue) { match se.payload { Name(n) { srcName = n; } _ { } } }
            if (srcName == NO_SYM) {
                self.err(stringOf("`for x in` needs an iterator held in a variable\nhelp: bind it to a local first"));
            }
            return self.iterLoop(it, elem.base, elem.name, srcName, se.kind, se.structName,
                                 NO_STMT, NO_STMT);
        }
        // An element that is a value and not a struct cannot be lent: writing through it would
        // write a copy. Said here when the type is already concrete; a template's element is
        // held to it once it is stamped.
        if (lend && elem.base != Lit.TypeVar && (elem.base != Lit.Struct || namedScalar(elem.base, elem.name))) {
            self.err(format("`for x in &xs` needs struct elements, found `{}`\nnote: a `{}` is copied, so writing through `x` would change only the copy\nhelp: write `xs[i] = ...` to change an element",
                            typeMangleName(elem.base, elem.name), typeMangleName(elem.base, elem.name)));
        }

        seq: long = self.forSeq;
        self.forSeq = seq + 1;
        tag: str = "p";
        if (lend) { tag = "w"; }
        pStruct: Sym = intern(typeMangleName(elem.base, elem.name));
        pv: Sym = self.declareLocal(internString(format("$for{}{}", tag, seq)), Lit.Ptr, pStruct);
        nv: Sym = self.declareLocal(internString(format("$forn{}", seq)), Lit.Long, NO_SYM);
        iv: Sym = self.declareLocal(internString(format("$fori{}", seq)), Lit.Long, NO_SYM);
        ids: Vec<long>;
        ids.push(self.forDecl(pv, Lit.Ptr, pStruct));
        ids.push(self.forDecl(nv, Lit.Long, NO_SYM));
        ids.push(self.forDecl(iv, Lit.Long, NO_SYM));

        setup: Vec<long>;
        if (lend) { setup.push(self.exprStmt(self.ast.unary(Op.AddressOf, self.clonePlace(src), Lit.Long))); }
        base: NodeId = src;
        len: NodeId = self.clonePlace(src);
        if (shape == FOR_ARRAY) { base = self.wholeOf(base); len = self.wholeOf(len); }
        // `$forsK = xs.asSlice();`, then its pointer and length as a slice's. A small `asSlice`
        // inlines, and the loop is the same bare index loop a slice's is.
        if (shape == FOR_VIEW) {
            noArgs: Vec<NodeId>;
            q: Quoter = self.quoter();
            view: NodeId = q.qMethod(&self.ast, self.clonePlace(src), "asSlice", noArgs);
            sv: Sym = self.inferPair(internString(format("$fors{}", seq)), view, &setup);
            infer: Sym = intern(INFER_SPELLING);
            base = self.nameRef(sv, Lit.Void, infer);
            len = self.nameRef(sv, Lit.Void, infer);
        }
        setup.push(self.exprStmt(self.ast.binary(Op.Assignment, self.nameRef(pv, Lit.Ptr, pStruct),
                                                 self.fieldOf(base, "ptr"), Lit.Ptr)));
        setup.push(self.exprStmt(self.ast.binary(Op.Assignment, self.nameRef(nv, Lit.Long, NO_SYM),
                                                 self.fieldOf(len, "len"), Lit.Long)));
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(setup) });
        ids.push(self.ast.addStmt(StmtKind.Unsafe, self.ast.blockStmts.len() - 1));
        ids.push(self.exprStmt(self.ast.binary(Op.Assignment, self.nameRef(iv, Lit.Long, NO_SYM),
                                               self.numberLit(0, Lit.Long), Lit.Long)));

        // The element, at the head of the body.
        xr: Sym = self.declareLocal(it.text, elem.base, elem.name);
        head: Vec<long>;
        head.push(self.forDecl(xr, elem.base, elem.name));
        self.ast.indexes.push(IndexNode { name: NO_SYM, base: self.nameRef(pv, Lit.Ptr, pStruct),
                                          index: self.nameRef(iv, Lit.Long, NO_SYM), whole: false,
                                          rawPointerBase: false, sliceStart: NO_NODE,
                                          sliceEnd: NO_NODE, at: NO_SYM });
        at: NodeId = self.ast.leaf(Op.ArrayIndex, Payload.Index(self.ast.indexes.len() - 1), Lit.Int);
        head.push(self.exprStmt(self.ast.binary(Op.Assignment, self.nameRef(xr, elem.base, elem.name),
                                                at, elem.base)));
        self.loopDepth = self.loopDepth + 1;
        body: long = self.parseBlock();
        self.loopDepth = self.loopDepth - 1;
        self.popScope();
        for j in 0..self.ast.blockLen(body) { head.push(self.ast.stmtIdAt(body, j)); }

        cond: NodeId = self.ast.binary(Op.LessThan, self.nameRef(iv, Lit.Long, NO_SYM),
                                       self.nameRef(nv, Lit.Long, NO_SYM), Lit.Bool);
        inc: NodeId = self.ast.binary(Op.Addition, self.nameRef(iv, Lit.Long, NO_SYM),
                                      self.numberLit(1, Lit.Long), Lit.Long);
        stepIds: Vec<long>;
        stepIds.push(self.exprStmt(self.ast.binary(Op.Assignment, self.nameRef(iv, Lit.Long, NO_SYM),
                                                   inc, Lit.Long)));
        self.ast.whiles.push(WhileNode { cond: cond, body: self.ast.addBlock(head),
                                         step: self.ast.addBlock(stepIds) });
        ids.push(self.ast.addStmt(StmtKind.While, self.ast.whiles.len() - 1));
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(ids) });
        return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
    }

    forDecl &self n:Sym k:Lit s:Sym -> long {
        self.ast.decls.push(VarDeclNode { name: n, kind: k, structName: s, isArray: false, count: 0,
                                          conv: Conv.None, isVariadic: false, elemKind: Lit.Void,
                                          elemStruct: NO_SYM, init: NO_NODE });
        return self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1);
    }
    exprStmt &self v:NodeId -> long {
        self.ast.exprStmts.push(ExprStmtNode { value: v });
        return self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1);
    }
    fieldOf &self base:NodeId f:str -> NodeId {
        self.ast.fields.push(FieldNode { base: base, name: intern(f) });
        return self.ast.leaf(Op.FieldAccess, Payload.Field(self.ast.fields.len() - 1), Lit.Void);
    }
    // `xs[..]`: the whole of an array, as a slice.
    wholeOf &self base:NodeId -> NodeId {
        self.ast.indexes.push(IndexNode { name: NO_SYM, base: base, index: NO_NODE, whole: true,
                                          rawPointerBase: false, sliceStart: NO_NODE,
                                          sliceEnd: NO_NODE, at: NO_SYM });
        return self.ast.leaf(Op.ArrayIndex, Payload.Index(self.ast.indexes.len() - 1), Lit.Int);
    }
    // A second copy of a place `placeTy` accepted (a name, a field of one, a capture), for the
    // loop's setup to read it more than once. Each node of a tree has one parent.
    clonePlace &self id:NodeId -> NodeId {
        e: Expr = self.ast.expr(id);
        p: Payload = e.payload;
        np: Payload = e.payload;
        match p {
            Field(f) {
                fd: FieldNode = self.ast.fields.get(f);
                self.ast.fields.push(FieldNode { base: self.clonePlace(fd.base), name: fd.name });
                np = Payload.Field(self.ast.fields.len() - 1);
            }
            Sub(v) { np = Payload.Sub(self.clonePlace(v)); }
            _ { }
        }
        e.payload = np;
        return self.ast.addExpr(e);
    }

    // The type of a place, as far as the parser knows types: a local's or a global's declared
    // type, a captured variable's, and a field's through the registry (a struct's, or a
    // template's under the arguments its instance was requested with). `ok` is false for anything
    // else (a call, an index), whose type only the checker knows.
    placeTy &self id:NodeId -> PlaceTy {
        no: PlaceTy = PlaceTy { kind: Lit.Void, name: NO_SYM, isArray: false, ok: false };
        e: Expr = self.ast.expr(id);
        p: Payload = e.payload;
        if (e.op == Op.Lvalue) {
            n: Sym = NO_SYM;
            match p { Name(x) { n = x; } _ { return no; } }
            i: long = self.scopes.len();
            while (i > 0) {
                i = i - 1;
                b: Binding = self.scopes.get(i);
                if (b.renamed == n) {
                    return PlaceTy { kind: b.kind, name: b.structName, isArray: b.isArray, ok: true };
                }
            }
            // A global this module declares, or one a module it includes does (`gOutModules`
            // read from the module that writes the package's metadata).
            gi: long = self.globalNamed(nameOf(n), self.currentModule());
            if (gi < 0) { return self.laterGlobalTy(nameOf(n)); }
            g: GlobalDef = gReg.globalDef(gi);
            return PlaceTy { kind: g.kind, name: g.structName, isArray: g.isArray, ok: true };
        }
        if (e.op != Op.FieldAccess) { return no; }
        // A capture is a field of the closure's own struct, typed when it was read.
        if (e.kind != Lit.Void) { return PlaceTy { kind: e.kind, name: e.structName, isArray: false, ok: true }; }
        fd: FieldNode = FieldNode { base: NO_NODE, name: NO_SYM };
        match p { Field(f) { fd = self.ast.fields.get(f); } _ { return no; } }
        bt: PlaceTy = self.placeTy(fd.base);
        if (!bt.ok || bt.isArray || !(bt.kind == Lit.Struct || bt.kind == Lit.Ref) || bt.name == NO_SYM) { return no; }
        return self.fieldTy(bt.name, fd.name);
    }

    // A global this module declares further down (`for w in RESERVED` above `RESERVED: ...`): the
    // type is read from its declaration, found by scanning the module's text for a top-level
    // `name:` and parsing what follows with the parser's own cursor put back afterwards. The
    // declaration itself is read in its turn, as any other; only its type is looked at early.
    // Only an unresolved `for x in` pays for the scan.
    laterGlobalTy &self spelled:str -> PlaceTy {
        no: PlaceTy = PlaceTy { kind: Lit.Void, name: NO_SYM, isArray: false, ok: false };
        bare: str = lastComponentOf(spelled);
        scan: Lexer = lexerOf(self.lx.src);
        depth: long = 0;
        startsDecl: bool = true;        // the next token at depth 0 may begin a declaration
        loop {
            t: Token = scan.next();
            if (t.kind == Tok.FileEnd) { return no; }
            if (t.kind == Tok.LeftCurly) { depth = depth + 1; startsDecl = false; continue; }
            if (t.kind == Tok.RightCurly) { depth = depth - 1; startsDecl = depth == 0; continue; }
            if (depth != 0) { continue; }
            if (t.kind == Tok.Semicolon) { startsDecl = true; continue; }
            if (t.kind == Tok.Id && startsDecl) {
                w: str = nameOf(t.text);
                if (w == "pub" || w == "pkg" || w == "local" || w == "var") { continue; }
                if (w == bare) {
                    at: Lexer = scan;
                    if (scan.next().kind == Tok.Colon) { return self.typeAt(at); }
                }
            }
            startsDecl = false;
        }
        return no;
    }

    // The type a global's declaration spells, the lexer standing on its name: `[T; N]` an array of
    // T, anything else a type. Read with the parser's cursor, which is put back as it was.
    typeAt &self at:Lexer -> PlaceTy {
        savedLx: Lexer = self.lx;
        savedCur: Token = self.cur;
        savedPeeked: Token = self.peeked;
        savedHas: bool = self.hasPeeked;
        savedCurPos: long = self.curPos;
        savedPeekPos: long = self.peekPos;
        self.lx = at;
        self.hasPeeked = false;
        self.advance();                 // the colon after the name
        self.advance();                 // the type's first token
        // A type declared between here and the global is not declared yet: named as this
        // module's, which it will be, as a pointee's is. One nothing declares is refused where the
        // global itself is read.
        self.inPointee = self.inPointee + 1;
        out: PlaceTy = PlaceTy { kind: Lit.Void, name: NO_SYM, isArray: false, ok: true };
        if (self.eat(Tok.LeftSquare)) {
            elem: TypeRef = self.parseTypeRef();
            out = PlaceTy { kind: elem.base, name: elem.name, isArray: self.check(Tok.Semicolon), ok: true };
            if (!out.isArray) { out.kind = Lit.Slice; out.name = intern(typeMangleName(elem.base, elem.name)); }
        } else {
            t: TypeRef = self.parseTypeRef();
            out = PlaceTy { kind: t.base, name: t.name, isArray: false, ok: true };
        }
        self.inPointee = self.inPointee - 1;
        self.lx = savedLx;
        self.cur = savedCur;
        self.peeked = savedPeeked;
        self.hasPeeked = savedHas;
        self.curPos = savedCurPos;
        self.peekPos = savedPeekPos;
        return out;
    }

    fieldTy &self owner:Sym f:Sym -> PlaceTy {
        no: PlaceTy = PlaceTy { kind: Lit.Void, name: NO_SYM, isArray: false, ok: false };
        si: long = gReg.findStructSym(owner);
        if (si >= 0) {
            d: StructDef = gReg.structDef(si);
            k: long = gReg.findFieldSym(d, f);
            if (k < 0) { return no; }
            fdef: FieldDef = gReg.fieldAt(d, k);
            return PlaceTy { kind: fdef.kind, name: fdef.structName, isArray: fdef.isArray, ok: true };
        }
        // A template, named as itself inside its own methods, or an instance of one.
        ti: long = gReg.findTemplateSym(owner);
        r: long = NOT_FOUND;
        if (ti < 0) {
            r = gReg.findRequestSym(owner);
            if (r >= 0) { ti = gReg.findTemplateSym(gReg.requestAt(r).base); }
        }
        if (ti < 0) { return no; }
        t: GTemplate = gReg.templateDef(ti);
        for k in 0..t.fieldCount {
            g: GField = gReg.gFieldAt(t, k);
            if (g.name == f) {
                ty: TypeRef = g.kind;
                if (r >= 0) { ty = self.substTy(ty, t, gReg.requestAt(r), 0); }
                return PlaceTy { kind: ty.base, name: ty.name, isArray: g.isArray, ok: true };
            }
        }
        return no;
    }

    // `ty` written inside template `t`, under the arguments of request `r`: a parameter becomes
    // its argument, through instances (`Vec<T>` -> `Vec<long>`, asked for here as any other use
    // would be) and pointers.
    substTy &self ty:TypeRef t:GTemplate r:GRequest depth:long -> TypeRef {
        if (depth > 16) { return ty; }
        if (ty.base == Lit.TypeVar) {
            k: long = gReg.gParamIndex(t, ty.name);
            if (k >= 0 && k < r.argCount) { return gReg.gArgAt(r, k); }
            return ty;
        }
        if ((ty.base == Lit.Ptr || ty.base == Lit.Ref || ty.base == Lit.Slice) && ty.name != NO_SYM) {
            inner: TypeRef = self.substTy(unmangledType(nameOf(ty.name)), t, r, depth + 1);
            return TypeRef { base: ty.base, name: intern(typeMangleName(inner.base, inner.name)) };
        }
        if (ty.base == Lit.Struct && ty.name != NO_SYM) {
            q: long = gReg.findRequestSym(ty.name);
            if (q < 0) {
                // A parameter spelled as a type name (`T` as the pointee of a mangled `ptr_T`).
                if (gReg.gParamIndex(t, ty.name) >= 0) {
                    return self.substTy(TypeRef { base: Lit.TypeVar, name: ty.name }, t, r, depth + 1);
                }
                return ty;
            }
            inner: GRequest = gReg.requestAt(q);
            args: Vec<TypeRef>;
            changed: bool = false;
            for k in 0..inner.argCount {
                was: TypeRef = gReg.gArgAt(inner, k);
                now: TypeRef = self.substTy(was, t, r, depth + 1);
                if (now.base != was.base || now.name != was.name) { changed = true; }
                args.push(now);
            }
            if (!changed) { return ty; }
            return self.instanceOf(inner.base, args);
        }
        return ty;
    }

    // The element type of an iterator: the `T` of the `Iter<T>` its type implements, directly or
    // through the template it is an instance of. Void when it implements none.
    iterElemOf &self n:Sym -> TypeRef { return self.traitElemOf(n, "Iter"); }

    // The `T` of the one-parameter core trait `trait<T>` (`Iter`, `AsSlice`) that `n` implements,
    // directly or through the template it is an instance of. Void when it implements none.
    traitElemOf &self n:Sym trait:str -> TypeRef {
        if (n == NO_SYM) { return typeRefOf(Lit.Void); }
        r: long = gReg.findRequestSym(n);
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            if (lastComponentOf(nameOf(im.trait.name)) != trait || im.trait.argCount != 1) { continue; }
            if (im.structName == n) { return borrowedElem(gReg.traitArgAt(im.trait, 0)); }
            if (r >= 0 && im.structName == gReg.requestAt(r).base) {
                ti: long = gReg.findTemplateSym(im.structName);
                if (ti < 0) { continue; }
                return borrowedElem(self.substTy(gReg.traitArgAt(im.trait, 0), gReg.templateDef(ti),
                                                 gReg.requestAt(r), 0));
            }
        }
        return typeRefOf(Lit.Void);
    }
}

// The implementation `type T = distinct B with Trait` writes, as source; "" for a trait it does
// not know. The binary operators take another `T` (`Meters + Meters`), as the base's take its own.
local distinctImpl trait:str t:str b:str -> str {
    ops: str = "";
    sym: str = "";
    if (trait == "Add") { ops = "add"; sym = "+"; }
    else if (trait == "Sub") { ops = "sub"; sym = "-"; }
    else if (trait == "Mul") { ops = "mul"; sym = "*"; }
    else if (trait == "Div") { ops = "div"; sym = "/"; }
    else if (trait == "Rem") { ops = "rem"; sym = "%"; }
    else if (trait == "BitAnd") { ops = "bitand"; sym = "&"; }
    else if (trait == "BitOr") { ops = "bitor"; sym = "|"; }
    else if (trait == "BitXor") { ops = "bitxor"; sym = "^"; }
    else if (trait == "Shl") { ops = "shl"; sym = "<<"; }
    else if (trait == "Shr") { ops = "shr"; sym = ">>"; }
    if (ops.len > 0) {
        return keepString(format("methods {} for {}<{}> {{ {} self o:{} -> {} {{ return ((self as {}) {} (o as {})) as {}; }} }}\n",
                                 t, trait, t, ops, t, t, b, sym, b, t));
    }
    if (trait == "Not") {
        return keepString(format("methods {} for Not {{ not self -> {} {{ return (~(self as {})) as {}; }} }}\n", t, t, b, t));
    }
    if (trait == "Eq") {
        return keepString(format("methods {} for Eq<{}> {{ eq &self o:{} -> bool {{ return (self as {}) == (o as {}); }} }}\n",
                                 t, t, t, b, b));
    }
    if (trait == "Ord") {
        return keepString(format("methods {} for Ord {{ cmp &self o:{} -> int {{ x: {} = self as {}; y: {} = o as {}; if (x < y) {{ return -1; }} if (x > y) {{ return 1; }} return 0; }} }}\n",
                                 t, t, b, b, b, b));
    }
    if (trait == "Hash") {
        return keepString(format("methods {} for Hash {{ hash &self -> u64 {{ x: {} = self as {}; return x.hash(); }} }}\n", t, b, b));
    }
    return "";
}

// `&T` as an element: a borrow of a struct stays one; of anything else it is the value, as `&T`
// written in a type is (`parseTypeRef`).
local borrowedElem t:TypeRef -> TypeRef {
    if (t.base != Lit.Ref || t.name == NO_SYM) { return t; }
    inner: TypeRef = unmangledType(nameOf(t.name));
    if ((inner.base == Lit.Struct && !namedScalar(inner.base, inner.name)) || inner.base == Lit.TypeVar) { return t; }
    return inner;
}

// ─── sum-type layout ─────────────────────────────────────────────────────────


// Lay a sum type out and register it as an ordinary aggregate.
//
// The layout is the standard tagged union: the tag at offset 0, then every variant's payload from
// one shared offset, so the variants overlap and the size is the largest of them plus the tag,
// not their sum. That offset is aligned for the widest thing any variant puts there, so reading a
// payload costs exactly what reading a struct field costs.
//
// The fields are also registered as a struct, at those overlapping offsets. That is the point:
// an enum value is then an ordinary aggregate everywhere downstream.
pub layoutEnum name:Sym backing:Lit inout variants:Vec<VariantDef> inout payloads:Vec<FieldDef> -> long {
    tagSize: long = typeInfo(backing).size;
    maxAlign: long = tagSize;
    for i in 0..payloads.len() {
        f: FieldDef = payloads.get(i);
        a: long = typeSizeOf(f.kind, f.structName);
        if (isAggregate(f.kind)) { a = 8; }
        if (a > maxAlign) { maxAlign = a; }
    }
    payloadOffset: long = alignUp(tagSize, maxAlign);

    end: long = tagSize;
    for v in 0..variants.len() {
        var: VariantDef = variants.get(v);
        cursor: long = payloadOffset;            // every variant starts at the same place
        for k in 0..var.payloadCount {
            at: long = var.firstPayload + k;
            p: Placed = placeField(cursor, payloads.get(at));
            payloads.set(at, p.field);
            cursor = p.next;
        }
        if (cursor > end) { end = cursor; }
    }
    return alignUp(end, 8);                      // an aggregate aligns to 8
}

methods Parser {
    // ─── enums ───────────────────────────────────────────────────────────────

    // `enum Name: backing { A, B = 5, C(long, long) }`. Give a variant a payload and the enum
    // becomes a tagged union: a real sum type. Which one you declared is decided by whether you
    // wrote a payload, not by a second keyword.
    parseEnumDecl &self -> long {
        name: Token = self.expect(Tok.Id);
        self.declName = name.text;
        if (self.check(Tok.LessThan)) { return self.parseGenericEnum(name.text); }
        self.requireTypeNameFree(nameOf(name.text));
        q: Sym = self.qualify(nameOf(name.text));

        // A sum type may hold itself behind an indirection too: `Pair(Box<Tree>, Box<Tree>)` is
        // what a syntax tree is. The placeholder is a struct entry, because that is what a sum
        // type resolves through. It is retracted at the `}` if the enum turns out to be a backed
        // one.
        at: long = regBeginStruct(q, self.lx.currentPackage);
        backing: Lit = Lit.Int;
        if (self.eat(Tok.Colon)) { backing = self.parseTypeRef().base; }
        self.expect(Tok.LeftCurly);

        variants: Vec<VariantDef>;
        payloads: Vec<FieldDef>;
        next: long = 0;
        hasPayload: bool = false;

        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            vname: Token = self.expect(Tok.Id);
            first: long = payloads.len();
            n: long = 0;
            if (self.eat(Tok.LeftParen)) {
                hasPayload = true;
                while (!self.check(Tok.RightParen) && !self.check(Tok.FileEnd)) {
                    t: TypeRef = self.parseTypeRef();
                    payloads.push(FieldDef { name: enumPayloadField(nameOf(vname.text), n),
                                             kind: t.base, structName: t.name, offset: 0,
                                             isArray: false, count: 0 });
                    n = n + 1;
                    self.eat(Tok.Comma);
                }
                self.expect(Tok.RightParen);
            }
            value: long = next;
            // `= 5`, `= -11`, `= 0xFFFF_FFFF_FFFF_FFFF`: an integer literal, held to the backing.
            if (self.eat(Tok.Equals)) {
                neg: bool = self.eat(Tok.Dash);
                wide: bool = self.check(Tok.U64Literal);
                lit: Token = self.cur;
                if (!wide && !self.check(Tok.LongLiteral)) { lit = self.expect(Tok.IntLiteral); }
                else { lit = self.advance(); }
                value = lit.num;
                if (neg) { value = 0 - value; }
                if ((wide && (neg || backing != Lit.U64)) || (!wide && !literalFits(value, backing))) {
                    shown: String;
                    if (neg) { shown.push('-'); }
                    shown.pushString(format("{}", lit.num as u64));
                    self.err(format("literal `{}` out of range for `{}`\nnote: the value of `{}.{}` must fit the enum's backing type",
                                    shown, typeName(backing), nameOf(name.text), nameOf(vname.text)));
                }
            }
            next = value + 1;
            variants.push(VariantDef { name: vname.text, value: value,
                                       firstPayload: first, payloadCount: n });
            self.eat(Tok.Comma);
        }
        self.expect(Tok.RightCurly);

        size: long = 0;
        if (hasPayload) { size = layoutEnum(q, backing, &variants, &payloads); }
        regAddEnum(q, backing, variants, hasPayload);

        // A sum type is also an aggregate: register the tag and every payload as struct fields, so
        // everything downstream reads it the way it reads any other struct.
        if (hasPayload) {
            fields: Vec<FieldDef>;
            tagCursor: long = 0;
            want: FieldDef = FieldDef { name: intern(enumTagField()), kind: backing,
                                        structName: NO_SYM, offset: 0, isArray: false, count: 0 };
            p: Placed = placeField(tagCursor, want);
            fields.push(p.field);
            fields.extend(payloads);
            regFinishStruct(at, fields, size, true);
        } else {
            regAbandonStruct(at);
        }

        self.ast.structDecls.push(q);
        st: long = self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1);
        return st;
    }

    // ─── match ───────────────────────────────────────────────────────────────

    // `match x { Ok(v) { } Err(_) { } }`: an arm is a variant, the names it binds that variant's
    // payload to, and a block. There is no arrow, since every other construct here writes a block
    // straight after what introduces it.
    //
    // The subject is any expression. A local or a global is matched where it is. Any other place
    // the parser can type (`h.s`, `a.b.c`) is first copied into a hidden local of that type, and
    // the match reads that: `$matchN: T; $matchN = h.s;`. That is a move, as `x = h.s` is, unless
    // the match borrows (`match &h.s`, `$bmatchN`, which the checker makes a borrow of the place).
    // An expression whose type only the checker knows (a call, a method's borrow, an element) is
    // held the same way, in a local of whatever type its value turns out to have (`<infer>`). Its
    // arms are then read by name (`?Some`) and held to that type by the checker (`resolveMatch`).
    // The hidden locals and the match are one block, so a temporary is released after the match.
    // `match &f()` holds the value in `$mownN` and matches a borrow of it, so nothing moves out.
    parseMatch &self -> long {
        borrowedMatch: bool = self.eat(Tok.Ampersand);
        subj: NodeId = self.parseExpr();
        se: Expr = self.ast.expr(subj);
        pt: PlaceTy = self.placeTy(subj);
        if (pt.ok && (isInferType(pt.kind, pt.name) || pt.isArray)) { pt.ok = false; }
        what: String = self.spellPlace(subj);
        deferred: bool = !pt.ok;
        infer: Sym = intern(INFER_SPELLING);
        bound: Sym = NO_SYM;
        isName: bool = false;
        if (se.op == Op.Lvalue) { match se.payload { Name(x) { bound = x; isName = true; } _ { } } }
        subjKind: Lit = pt.kind;
        subjName: Sym = pt.name;
        if (isName && !self.isLocalName(bound)) {
            gi: long = gReg.findGlobalSym(self.qualify(nameOf(bound)));
            if (gi >= 0) { bound = gReg.globalDef(gi).name; }
            else if (!pt.ok) { self.err(format("cannot find value `{}` in this scope", nameOf(bound))); }
        }
        pre: Vec<long>;
        if (!isName || borrowedMatch) {
            seq: long = self.matchSeq;
            self.matchSeq = self.matchSeq + 1;
            // Numbered rather than left to `declareLocal`'s shadow rename: two matches in sibling
            // blocks would otherwise both be `$match` and share one stack slot. A borrowing match's
            // local is `$bmatchN`, which the checker makes a borrow of what it reads (`bmMatch`).
            hidden: Sym = NO_SYM;
            if (borrowedMatch) { hidden = internString(format("$bmatch{}", seq)); }
            else { hidden = internString(format("$match{}", seq)); }
            if (deferred) {
                if (borrowedMatch && !self.isPlace(subj)) {
                    own: Sym = self.inferPair(internString(format("$mown{}", seq)), subj, &pre);
                    subj = self.nameRef(own, Lit.Void, infer);
                }
                bound = self.inferPair(hidden, subj, &pre);
                subjKind = Lit.Void;
                subjName = infer;
            } else {
                renamed: Sym = self.declareLocal(hidden, pt.kind, pt.name);
                self.ast.decls.push(VarDeclNode { name: renamed, kind: pt.kind, structName: pt.name,
                                                  isArray: false, count: 0, conv: Conv.None,
                                                  isVariadic: false, elemKind: Lit.Void,
                                                  elemStruct: NO_SYM, init: NO_NODE });
                pre.push(self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1));
                lhs: NodeId = self.nameRef(renamed, pt.kind, pt.name);
                self.ast.exprStmts.push(ExprStmtNode { value: self.ast.binary(Op.Assignment, lhs, subj, pt.kind) });
                pre.push(self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1));
                bound = renamed;
            }
        }

        si: SumInfo = self.sumInfoOf(NO_SYM);
        if (!deferred) {
            si = self.sumInfoOf(subjName);
            if (si.enumAt < 0 && si.tmplAt < 0) {
                // An instance of a template nothing declares (`Result<long, long>` with no
                // include): the type is what is wrong, not the match.
                ri: long = gReg.findRequestSym(subjName);
                if (ri >= 0 && gReg.findTemplateSym(gReg.requestAt(ri).base) < 0) {
                    tb: str = lastComponentOf(nameOf(gReg.requestAt(ri).base));
                    self.err(format("cannot find type `{}` in this scope{}", tb, stdlibHint(tb)));
                }
                self.err(format("`{}` is not an enum\nnote: `match` reads the variants of an enum",
                                what));
            }
        }
        self.expect(Tok.LeftCurly);

        arms: Vec<ArmNode>;
        covered: Vec<Sym>;
        wildcard: bool = false;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            vname: Token = self.expect(Tok.Id);
            variant: Sym = vname.text;
            vi: long = NOT_FOUND;
            if (nameOf(variant) == "_") { variant = NO_SYM; wildcard = true; }
            else {
                if (!deferred) {
                    vi = self.sumVariantIndex(si, nameOf(variant));
                    if (vi < 0) {
                        self.err(format("no variant `{}` in enum `{}`", nameOf(variant), nameOf(subjName)));
                    }
                }
                if (self.symSeen(covered, variant)) {
                    self.err(format("duplicate match arm for variant `{}`", nameOf(variant)));
                }
                covered.push(variant);
            }

            // The names first, before the arm's scope exists: what each one is declared as comes
            // from the variant, so the payload has to be known before any of them can be declared.
            raw: Vec<Sym>;
            // A variant that carries values must have them all named (or discarded with `_`), so
            // an arm cannot quietly ignore what it was handed. Checked as the list is read rather
            // than by counting afterwards, so the report lands on what is missing instead of on
            // the `)` past it. A deferred match's are counted by the checker.
            arity: long = 0;
            if (vi >= 0) { arity = self.sumVariantArity(si, vi); }
            if (deferred && variant != NO_SYM) {
                if (self.eat(Tok.LeftParen)) {
                    while (!self.check(Tok.RightParen) && !self.check(Tok.FileEnd)) {
                        if (raw.len() > 0) { self.expect(Tok.Comma); }
                        raw.push(self.expect(Tok.Id).text);
                    }
                    self.expect(Tok.RightParen);
                }
            } else if (arity > 0) {
                if (!self.check(Tok.LeftParen)) {
                    self.err(format("variant `{}` carries {}\nhelp: name what it carries: `{}(...)`",
                                    nameOf(variant), plural(arity, "value"), nameOf(variant)));
                }
                self.advance();
                for r in 0..arity {
                    if (self.check(Tok.RightParen)) {
                        self.err(format("too few names for variant `{}`: expected {}, found {}",
                                        nameOf(variant), arity, r));
                    }
                    if (r > 0) { self.expect(Tok.Comma); }
                    raw.push(self.expect(Tok.Id).text);
                }
                if (!self.check(Tok.RightParen)) {
                    self.err(format("variant `{}` carries only {}", nameOf(variant), plural(arity, "value")));
                }
                self.expect(Tok.RightParen);
            } else if (self.check(Tok.LeftParen)) {
                if (vi >= 0) {
                    self.err(format("variant `{}` carries no payload", nameOf(variant)));
                }
                self.err(stringOf("`_` binds nothing\nnote: `_` stands for every remaining variant, so it takes no names"));
            }

            // Each arm is its own scope, so its bindings live and die with it and two arms may
            // bind the same name, which for a Result is the ordinary case, both arms wanting to
            // call theirs `e`.
            self.pushScope();
            binds: Vec<Sym>;
            prologue: Vec<long>;
            k: long = 0;
            while (k < raw.len()) {
                nm: Sym = raw.get(k);
                if (nameOf(nm) == "_") { binds.push(nm); k = k + 1; continue; }
                if (self.symSeen(binds, nm)) {
                    self.err(format("`{}` is bound more than once in the same arm", nameOf(nm)));
                }
                // The binding becomes an ordinary local at the head of the arm: `v: T;` then
                // `v = subject.$V$k;`: declared and assigned exactly as the programmer would
                // write it. Everything downstream then treats a bound payload as the local it is:
                // type-checked, definitely initialized, and dropped at the end of the arm if it
                // owns something, with no pass having to learn what a binding is. A `_` reads
                // nothing at all: the value it would have named is never touched. In a deferred
                // match the type is the store's (`<infer>`).
                base: NodeId = self.nameRef(bound, subjKind, subjName);
                self.ast.fields.push(FieldNode { base: base,
                                                 name: enumPayloadField(nameOf(variant), k) });
                rhs: NodeId = self.ast.leafOf(Op.FieldAccess,
                                              Payload.Field(self.ast.fields.len() - 1),
                                              Lit.Void, NO_SYM);
                if (deferred) {
                    binds.push(self.inferPair(nm, rhs, &prologue));
                    k = k + 1;
                    continue;
                }
                t: TypeRef = self.sumPayloadType(si, variant, k);
                renamed: Sym = self.declareLocal(nm, t.base, t.name);
                binds.push(renamed);
                self.ast.decls.push(VarDeclNode { name: renamed, kind: t.base, structName: t.name,
                                                  isArray: false, count: 0, conv: Conv.None,
                                                  isVariadic: false, elemKind: Lit.Void,
                                                  elemStruct: NO_SYM, init: NO_NODE });
                prologue.push(self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1));
                lhs: NodeId = self.nameRef(renamed, t.base, t.name);
                asn: NodeId = self.ast.binary(Op.Assignment, lhs, rhs, t.base);
                self.ast.exprStmts.push(ExprStmtNode { value: asn });
                prologue.push(self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1));
                k = k + 1;
            }
            body: long = self.parseBlock();
            self.popScope();

            // The bindings go at the head of the arm's block, ahead of what was written in it.
            n2: long = self.ast.blockLen(body);
            for j in 0..n2 { prologue.push(self.ast.stmtIdAt(body, j)); }
            full: long = self.ast.addBlock(prologue);

            test: NodeId = NO_NODE;
            if (vi >= 0) {
                tb: NodeId = self.nameRef(bound, subjKind, subjName);
                tag: NodeId = NO_NODE;
                if (si.enumAt >= 0 && !gReg.enumDef(si.enumAt).hasPayload) {
                    // A backed enum is its integer, with no `$tag` to read: the arm compares the
                    // value itself. Through a cast, so a `&self` (which receives the value) and
                    // a local read the same, and the comparison is the backing integer's.
                    tag = self.ast.addExpr(Expr { op: Op.Cast, left: NO_NODE, right: NO_NODE,
                                                  kind: si.backing, structName: NO_SYM,
                                                  isParen: false, payload: Payload.Sub(tb) });
                } else {
                    self.ast.fields.push(FieldNode { base: tb, name: intern(enumTagField()) });
                    tag = self.ast.leafOf(Op.FieldAccess,
                                          Payload.Field(self.ast.fields.len() - 1),
                                          Lit.Void, NO_SYM);
                }
                want: NodeId = self.ast.leaf(Op.Literal,
                                             Payload.Num(self.sumVariantValue(si, vi)), si.backing);
                test = self.ast.binary(Op.IsEqual, tag, want, si.backing);
            }
            // A deferred arm's variant is spelled `?V` until the checker has held it to the type.
            armVariant: Sym = variant;
            if (deferred && variant != NO_SYM) { armVariant = internString(format("?{}", nameOf(variant))); }
            firstBind: long = self.ast.addNames(binds);
            arms.push(ArmNode { variant: armVariant, test: test, firstBind: firstBind,
                                bindCount: binds.len(), body: full });
        }
        self.expect(Tok.RightCurly);

        if (arms.len() == 0) {
            self.err(stringOf("this `match` has no arms"));
        } else {
            last: ArmNode = arms.get(arms.len() - 1);
            last.test = NO_NODE;
            arms.set(arms.len() - 1, last);
        }
        // A match with a gap is refused rather than falling through to nothing: the value always
        // holds one of the variants, so an unhandled one is a case the author did not think about.
        if (!wildcard && !deferred) {
            for v in 0..self.sumVariantCount(si) {
                want: Sym = self.sumVariantName(si, v);
                if (!self.symSeen(covered, want)) {
                    self.err(format("`match` does not cover variant `{}` of `{}`\nhelp: handle every variant, or add a `_` arm",
                                    nameOf(want), nameOf(subjName)));
                }
            }
        }

        firstArm: long = self.ast.arms.len();
        self.ast.arms.extend(arms);
        self.ast.matches.push(MatchNode { scrutinee: bound, firstArm: firstArm,
                                          armCount: arms.len() });
        st: long = self.ast.addStmt(StmtKind.Match, self.ast.matches.len() - 1);
        if (pre.len() == 0) { return st; }

        // The hidden locals live exactly as long as the match: one block.
        pre.push(st);
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(pre) });
        return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
    }

    // `name: <infer>; name = value;` into `out`: a local the checker types at its store. Answers
    // the name as declared (renamed when it shadows).
    inferPair &self name:Sym value:NodeId inout out:Vec<long> -> Sym {
        infer: Sym = intern(INFER_SPELLING);
        renamed: Sym = self.declareLocal(name, Lit.Void, infer);
        self.ast.decls.push(VarDeclNode { name: renamed, kind: Lit.Void, structName: infer, isArray: false,
                                          count: 0, conv: Conv.None, isVariadic: false, elemKind: Lit.Void,
                                          elemStruct: NO_SYM, init: NO_NODE });
        out.push(self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1));
        target: NodeId = self.nameRef(renamed, Lit.Void, infer);
        asn: NodeId = self.ast.binary(Op.Assignment, target, value, self.ast.expr(value).kind);
        self.ast.exprStmts.push(ExprStmtNode { value: asn });
        out.push(self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1));
        return renamed;
    }

    // Is `n` (as the parser renamed it) a local in scope?
    isLocalName &self n:Sym -> bool {
        i: long = self.scopes.len();
        while (i > 0) {
            i = i - 1;
            if (self.scopes.get(i).renamed == n) { return true; }
        }
        return false;
    }

    // A place as it was written, for a diagnostic: `h`, `h.s`; anything else is "this value".
    spellPlace &self id:NodeId -> String {
        out: String;
        e: Expr = self.ast.expr(id);
        p: Payload = e.payload;
        match p {
            Name(n) {
                if (e.op == Op.Lvalue) { out.pushStr(lastComponentOf(nameOf(n))); return out; }
            }
            Field(f) {
                if (e.op == Op.FieldAccess) {
                    out.pushString(self.spellPlace(self.ast.fields.get(f).base));
                    out.push('.');
                    out.pushStr(nameOf(self.ast.fields.get(f).name));
                    return out;
                }
            }
            _ { }
        }
        out.pushStr("this value");
        return out;
    }

    // ─── `?` ─────────────────────────────────────────────────────────────────
    //
    // `f()?` works in a function whose return type implements the core trait `Try<T, R>`, as the
    // standard library's Result and Option do. When `f()` breaks (`isBreak`), the function
    // returns its own type made from the failure (`fromResidual(residual())`); otherwise `f()?`
    // is the value that goes on (`output`). The failure is handed on as it is, with no
    // conversion, so `f()`'s `R` must be the function's.
    //
    // It is written out here, per statement, into what a person would write by hand (`wrapTry`).
    // The operand is held in a local of its own type and tested, and the statement goes in the
    // `else` with the `?` replaced by the output's local. Because of that, the ownership pass
    // releases the locals in scope on the early return as on any other, the evaluator can run
    // it, and the optimizer sees plain code (four small methods it inlines into the tag test a
    // `match` would make). The operand runs before the rest of the statement, so nothing with
    // an effect may come ahead of it (`tryOrder`).

    // `operand?`: noted, and replaced by the local its Ok value will be read through.
    tryHoleFor &self operand:NodeId -> NodeId {
        if (self.quoteDepth > 0) { self.err(stringOf("`?` is not supported inside a `quote`")); }
        if (!self.retOk) {
            self.err(stringOf("`?` needs a function to return from\nnote: `?` returns early, which is not supported in a closure or outside a function body"));
        }
        self.holdTryReturn();
        seq: long = self.uniq;
        self.uniq = self.uniq + 1;
        name: Sym = internString(format("$tok{}", seq));
        hole: NodeId = self.nameRef(name, Lit.Void, intern(INFER_SPELLING));
        self.tryHole.push(hole);
        self.tryOperand.push(operand);
        self.tryName.push(name);
        return hole;
    }

    // A function returning a scalar, a `str` or nothing has no type to return early as. Whether a
    // struct implements `Try` is the checker's to say (`Checker.readsTryLocal`): its
    // implementation may be declared below.
    holdTryReturn &self -> void {
        if (self.retTy.base == Lit.Struct && self.retTy.name != NO_SYM) { return; }
        self.err(format("`?` cannot be used in a function that returns `{}`\nnote: `?` returns the failure early, so the function must return a type implementing `Try`, such as `Result` or `Option`",
                        spellTypeName(typeMangleName(self.retTy.base, self.retTy.name))));
    }
    // The type a `?`'s early return names: the return type's template when it is generic (the
    // return's destination says the instance, as `Option.fromFlag` does), else the type.
    tryOwner &self -> Sym {
        if (self.retTy.base != Lit.Struct || self.retTy.name == NO_SYM) { return NO_SYM; }
        r: long = gReg.findRequestSym(self.retTy.name);
        if (r >= 0) { return gReg.requestAt(r).base; }
        if (gReg.findTemplateSym(self.retTy.name) >= 0) { return self.retTy.name; }
        return NO_SYM;
    }

    // Statement `id` held `?`s (those from `mark` on): each one's operand is matched ahead of it,
    // the first to run outermost. A declaration's initializer is its queued store's to hold.
    wrapTries &self id:long mark:long -> long {
        target: long = id;
        pending: bool = self.pendingInits.len() > 0;
        if (pending) {
            if (self.pendingInits.len() > 1) {
                self.err(stringOf("`?` is not supported in an array literal\nhelp: bind the element to a local first"));
            }
            target = self.pendingInits.get(0);
        }
        st: Stmt = self.ast.stmts.get(target);
        self.toMark = mark;
        self.toImpure = false;
        self.toCond = 0;
        self.toLhs = 0;
        self.toOrder.clear();
        if (st.kind == StmtKind.Destructure) {
            self.err(stringOf("`?` is not supported in a destructure that declares names\nhelp: bind the tuple first: `t: (A, B) = f()?;`"));
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { self.tryOrder(self.ast.exprStmts.get(st.at).value); }
        else if (st.kind == StmtKind.Return) { self.tryOrder(self.ast.returns.get(st.at).value); }
        else if (st.kind == StmtKind.If) { self.tryOrder(self.ast.ifs.get(st.at).cond); }
        else if (st.kind == StmtKind.VarDecl) { self.tryOrder(self.ast.decls.get(st.at).init); }
        else if (st.kind == StmtKind.Block) {
            b: long = self.ast.blockStmts.get(st.at).body;
            for k in 0..self.ast.blockLen(b) {
                s: Stmt = self.ast.stmtAt(b, k);
                if (s.kind == StmtKind.VarDecl) { self.tryOrder(self.ast.decls.get(s.at).init); }
                else if (s.kind == StmtKind.Expr) { self.tryOrder(self.ast.exprStmts.get(s.at).value); }
                else if (s.kind == StmtKind.Destructure) { self.tryOrder(self.ast.destructures.get(s.at).value); }
                else { break; }
            }
        }
        if (self.toOrder.len() != self.tryHole.len() - mark) {
            self.err(stringOf("`?` cannot be used here\nnote: in a loop's condition or header, or in an `else if` condition, it would run only once, ahead of the loop or the chain\nhelp: give it a statement of its own"));
        }
        inner: long = target;
        k: long = self.toOrder.len();
        first: bool = true;
        while (k > 0) {
            k = k - 1;
            before: long = -1;
            if (first && pending) { before = id; }
            inner = self.wrapTry(self.toOrder.get(k), inner, before);
            first = false;
        }
        if (pending) { self.pendingInits.clear(); }
        return inner;
    }

    // The `?`s under `id`, in the order they run, into `toOrder`: refused where moving the operand
    // ahead of the statement would change what runs (after a call or a store, in the right
    // operand of `&&`/`||`, in an assignment's target, in a macro's arguments).
    tryOrder &self id:NodeId -> void {
        if (id == NO_NODE) { return; }
        for k in self.toMark..self.tryHole.len() {
            if (self.tryHole.get(k) != id) { continue; }
            if (self.toLhs > 0) {
                self.err(stringOf("`?` is not supported in an assignment's target\nhelp: bind it to a local first"));
            }
            if (self.toCond > 0) {
                self.err(stringOf("`?` cannot be used in the right operand of `&&` or `||`\nnote: it would run whether or not the left operand decides the answer\nhelp: give it a statement of its own"));
            }
            if (self.toImpure) {
                self.err(stringOf("`?` cannot come after a call or a store in the same statement\nnote: `?` runs its operand ahead of the rest of the statement\nhelp: bind the earlier part to a local first"));
            }
            self.tryOrder(self.tryOperand.get(k));
            self.toImpure = false;            // what it leaves in the statement is a local
            self.toOrder.push(k);
            return;
        }
        e: Expr = self.ast.expr(id);
        if (e.op == Op.Assignment) {
            self.tryOrder(e.right);
            self.toLhs = self.toLhs + 1;
            self.tryOrder(e.left);
            self.toLhs = self.toLhs - 1;
            self.toImpure = true;
            return;
        }
        if (e.op == Op.LogicalAnd || e.op == Op.LogicalOr) {
            self.tryOrder(e.left);
            self.toCond = self.toCond + 1;
            self.tryOrder(e.right);
            self.toCond = self.toCond - 1;
            return;
        }
        if (e.left != NO_NODE || e.right != NO_NODE) { self.tryOrder(e.left); self.tryOrder(e.right); return; }
        p: Payload = e.payload;
        match p {
            Call(c) {
                cn: CallNode = self.ast.calls.get(c);
                if (e.op == Op.MacroCall) { self.toCond = self.toCond + 1; }
                self.tryOrder(cn.receiver);
                self.tryOrder(cn.callee);
                for k in 0..cn.argCount { self.tryOrder(self.ast.argAt(cn, k)); }
                if (e.op == Op.MacroCall) { self.toCond = self.toCond - 1; }
                self.toImpure = true;
            }
            Field(f) { self.tryOrder(self.ast.fields.get(f).base); }
            Index(i) {
                ix: IndexNode = self.ast.indexes.get(i);
                self.tryOrder(ix.base);
                self.tryOrder(ix.index);
                self.tryOrder(ix.sliceStart);
                self.tryOrder(ix.sliceEnd);
            }
            Lit(l) {
                ln: LitNode = self.ast.lits.get(l);
                for k in 0..ln.initCount { self.tryOrder(self.ast.inits.get(ln.firstInit + k).value); }
                self.tryOrder(ln.rest);
            }
            Sub(v) { self.tryOrder(v); }
            _ { }
        }
    }

    // `?` through the core trait `Try<T, R>` the function's return type implements:
    //
    //     { $tryN: <infer> = operand;
    //       if ($tryN.isBreak()) { return Ret.fromResidual($tryN.residual()); }
    //       else { $tokN: <infer> = $tryN.output(); inner } }
    //
    // `isBreak` says whether the value is the failure; `residual` takes the failure out and
    // `output` the value, each consuming the operand on its own path; `fromResidual` (a static of
    // the RETURN type's implementation) makes the early result from the failure. Each is a small
    // method of the library's, and the optimizer folds the four into the tag test and the moves
    // a hand-written match makes. `Ret` is named by its template where it is generic, so the
    // return's own type says the instance, as `Option.fromFlag` does.
    wrapTry &self k:long inner:long before:long -> long {
        infer: Sym = intern(INFER_SPELLING);
        seq: long = self.uniq;
        self.uniq = self.uniq + 1;
        pre: Vec<long>;
        subj: Sym = self.inferPair(internString(format("$try{}", seq)), self.tryOperand.get(k), &pre);
        q: Quoter = self.quoter();
        none: Vec<NodeId>;
        cond: NodeId = q.qMethod(&self.ast, self.nameRef(subj, Lit.Void, infer), "isBreak", none);
        rargs: Vec<NodeId>;
        rargs.push(q.qMethod(&self.ast, self.nameRef(subj, Lit.Void, infer), "residual", none));
        owner: Sym = self.tryOwner();
        if (owner == NO_SYM) { owner = self.retTy.name; }
        recv: NodeId = self.nameRef(owner, Lit.Struct, NO_SYM);
        self.ast.returns.push(ReturnNode { value: q.qMethod(&self.ast, recv, "fromResidual", rargs) });
        thenIds: Vec<long>;
        thenIds.push(self.ast.addStmt(StmtKind.Return, self.ast.returns.len() - 1));
        // The Ok side: `$tokN` (what the `?` was replaced by) is the output.
        tok: Sym = self.tryName.get(k);
        okBody: Vec<long>;
        self.ast.decls.push(VarDeclNode { name: tok, kind: Lit.Void, structName: infer, isArray: false,
                                          count: 0, conv: Conv.None, isVariadic: false, elemKind: Lit.Void,
                                          elemStruct: NO_SYM, init: NO_NODE });
        okBody.push(self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1));
        out: NodeId = q.qMethod(&self.ast, self.nameRef(subj, Lit.Void, infer), "output", none);
        self.ast.exprStmts.push(ExprStmtNode { value: self.ast.binary(Op.Assignment, self.nameRef(tok, Lit.Void, infer), out, Lit.Void) });
        okBody.push(self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1));
        if (before >= 0) { okBody.push(before); }
        okBody.push(inner);
        self.ast.ifs.push(IfNode { cond: self.ast.leaf(Op.Literal, Payload.Num(1), Lit.Bool),
                                   body: self.ast.addBlock(okBody), elseIf: -1 });
        elseAt: long = self.ast.ifs.len() - 1;
        if (before >= 0) {
            self.contIf = elseAt;
            self.contPre.clear();
            self.contPre.extend(okBody);
        }
        self.ast.ifs.push(IfNode { cond: cond, body: self.ast.addBlock(thenIds), elseIf: elseAt });
        pre.push(self.ast.addStmt(StmtKind.If, self.ast.ifs.len() - 1));
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(pre) });
        return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
    }

    // ─── compound assignment ─────────────────────────────────────────────────

    // The operator a compound assignment token stands for, or Op.Literal for none.
    compoundOp &self -> Op {
        k: Tok = self.cur.kind;
        if (k == Tok.PlusEq)    { return Op.Addition; }
        if (k == Tok.MinusEq)   { return Op.Subtraction; }
        if (k == Tok.StarEq)    { return Op.Multiplication; }
        if (k == Tok.SlashEq)   { return Op.Division; }
        if (k == Tok.PercentEq) { return Op.Modulus; }
        if (k == Tok.AmpEq)     { return Op.BitwiseAnd; }
        if (k == Tok.PipeEq)    { return Op.BitwiseOr; }
        if (k == Tok.CaretEq)   { return Op.BitwiseXor; }
        if (k == Tok.ShlEq)     { return Op.ShiftLeft; }
        if (k == Tok.ShrEq)     { return Op.ShiftRight; }
        return Op.Literal;
    }

    // `place op= value` is `place = place op value`, with the place evaluated once: an index that
    // has an effect (`a[f()] += 1`) is computed into a hidden local first, and the store and the
    // read both use it. So an operator a type implements (`Add`, `Sub`...) is what `+=` means for
    // it, and a float's rules are the float's.
    compoundAssign &self lhs:NodeId op:Op rhs:NodeId -> long {
        pre: Vec<long>;
        self.pushScope();
        once: NodeId = self.placeOnce(lhs, &pre);
        r: Expr = self.ast.expr(rhs);
        r.isParen = true;
        self.ast.setExpr(rhs, r);
        read: NodeId = self.copyPure(once);
        value: NodeId = self.ast.binary(op, read, rhs, higherPrecedence(self.ast.expr(read).kind, r.kind));
        asn: NodeId = self.ast.binary(Op.Assignment, once, value, self.ast.expr(once).kind);
        self.ast.exprStmts.push(ExprStmtNode { value: asn });
        st: long = self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1);
        self.popScope();
        if (pre.len() == 0) { return st; }
        pre.push(st);
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(pre) });
        return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
    }

    // The place, with every part that would have an effect computed once into a hidden local
    // ahead of it (`pre`). A place reached through a call is refused: making the call twice is not
    // what `+=` says, and holding its borrow in a local is not something code can do.
    placeOnce &self id:NodeId inout pre:Vec<long> -> NodeId {
        e: Expr = self.ast.expr(id);
        p: Payload = e.payload;
        match p {
            Field(f) {
                fd: FieldNode = self.ast.fields.get(f);
                fd.base = self.placeOnce(fd.base, pre);
                self.ast.fields.set(f, fd);
                return id;
            }
            Index(i) {
                ix: IndexNode = self.ast.indexes.get(i);
                if (ix.base != NO_NODE) { ix.base = self.placeOnce(ix.base, pre); }
                if (ix.index != NO_NODE && !self.isPure(ix.index)) {
                    n: Sym = self.inferPair(internString(format("$cidx{}", self.uniq)), ix.index, pre);
                    self.uniq = self.uniq + 1;
                    ix.index = self.nameRef(n, Lit.Long, NO_SYM);
                }
                self.ast.indexes.set(i, ix);
                return id;
            }
            Sub(v) {
                if (e.op == Op.Deref && !self.isPure(v)) {
                    n: Sym = self.inferPair(internString(format("$cptr{}", self.uniq)), v, pre);
                    self.uniq = self.uniq + 1;
                    e.payload = Payload.Sub(self.nameRef(n, Lit.Long, NO_SYM));
                    self.ast.setExpr(id, e);
                }
                return id;
            }
            _ { }
        }
        if (!self.isPure(id)) {
            self.err(stringOf("cannot use a compound assignment on a place reached through a call\nnote: the call would be made twice\nhelp: index it (`v[i] += 1`), or bind what the call returns first"));
        }
        return id;
    }

    // An expression with no effect: names, literals, fields, elements and arithmetic over them.
    isPure &self id:NodeId -> bool {
        if (id == NO_NODE) { return true; }
        e: Expr = self.ast.expr(id);
        if (e.op == Op.Assignment || e.op == Op.FunctionCall || e.op == Op.MethodCall || e.op == Op.MacroCall
            || e.op == Op.StructLit || e.op == Op.TupleLit) { return false; }
        if (e.left != NO_NODE || e.right != NO_NODE) { return self.isPure(e.left) && self.isPure(e.right); }
        p: Payload = e.payload;
        match p {
            Field(f) { return self.isPure(self.ast.fields.get(f).base); }
            Index(i) {
                ix: IndexNode = self.ast.indexes.get(i);
                return self.isPure(ix.base) && self.isPure(ix.index) && self.isPure(ix.sliceStart) && self.isPure(ix.sliceEnd);
            }
            Sub(v) { return self.isPure(v); }
            _ { }
        }
        return true;
    }

    // A second copy of an expression `isPure` accepted: every node of a tree has one parent.
    copyPure &self id:NodeId -> NodeId {
        if (id == NO_NODE) { return NO_NODE; }
        e: Expr = self.ast.expr(id);
        e.left = self.copyPure(e.left);
        e.right = self.copyPure(e.right);
        p: Payload = e.payload;
        match p {
            Field(f) {
                fd: FieldNode = self.ast.fields.get(f);
                self.ast.fields.push(FieldNode { base: self.copyPure(fd.base), name: fd.name });
                e.payload = Payload.Field(self.ast.fields.len() - 1);
            }
            Index(i) {
                ix: IndexNode = self.ast.indexes.get(i);
                ix.base = self.copyPure(ix.base);
                ix.index = self.copyPure(ix.index);
                ix.sliceStart = self.copyPure(ix.sliceStart);
                ix.sliceEnd = self.copyPure(ix.sliceEnd);
                self.ast.indexes.push(ix);
                e.payload = Payload.Index(self.ast.indexes.len() - 1);
            }
            Sub(v) { e.payload = Payload.Sub(self.copyPure(v)); }
            _ { }
        }
        return self.ast.addExpr(e);
    }

    symSeen &self xs:Vec<Sym> n:Sym -> bool {
        for k in 0..xs.len() { if (xs.get(k) == n) { return true; } }
        return false;
    }

    // ─── what a sum type says about its variants ─────────────────────────────

    sumInfoOf &self owner:Sym -> SumInfo {
        if (owner == NO_SYM) {
            return SumInfo { owner: owner, enumAt: NOT_FOUND, tmplAt: NOT_FOUND,
                             reqAt: NOT_FOUND, backing: Lit.Int };
        }
        e: long = gReg.findEnumSym(owner);
        if (e >= 0) {
            return SumInfo { owner: owner, enumAt: e, tmplAt: NOT_FOUND, reqAt: NOT_FOUND,
                             backing: gReg.enumDef(e).backing };
        }
        t: long = gReg.findTemplateSym(owner);
        if (t >= 0) {
            return SumInfo { owner: owner, enumAt: NOT_FOUND, tmplAt: t, reqAt: NOT_FOUND,
                             backing: Lit.Int };
        }
        // An instance. The request says which template and with what. Where even that is absent
        // (a generic use inside a template is a pattern, so it is never requested), the name still
        // spells its template, which is what `Option_T` -> `Option` recovers.
        r: long = gReg.findRequestSym(owner);
        if (r >= 0) {
            bs: Sym = gReg.requestAt(r).base;
            return SumInfo { owner: bs, enumAt: NOT_FOUND, tmplAt: gReg.findTemplateSym(bs),
                             reqAt: r, backing: Lit.Int };
        }
        ti: long = gReg.templateOfInstance(nameOf(owner));
        if (ti >= 0) {
            return SumInfo { owner: gReg.templateDef(ti).name, enumAt: NOT_FOUND, tmplAt: ti,
                             reqAt: NOT_FOUND, backing: Lit.Int };
        }
        return SumInfo { owner: owner, enumAt: NOT_FOUND, tmplAt: NOT_FOUND, reqAt: NOT_FOUND,
                         backing: Lit.Int };
    }

    sumVariantCount &self si:SumInfo -> long {
        if (si.enumAt >= 0) { return gReg.enumDef(si.enumAt).variantCount; }
        if (si.tmplAt >= 0) { return gReg.templateDef(si.tmplAt).variantCount; }
        return 0;
    }
    sumVariantName &self si:SumInfo k:long -> Sym {
        if (si.enumAt >= 0) { return gReg.variantAt(gReg.enumDef(si.enumAt), k).name; }
        return gReg.gVariantAt(gReg.templateDef(si.tmplAt), k).name;
    }
    sumVariantValue &self si:SumInfo k:long -> long {
        if (si.enumAt >= 0) { return gReg.variantAt(gReg.enumDef(si.enumAt), k).value; }
        return gReg.gVariantAt(gReg.templateDef(si.tmplAt), k).value;
    }
    sumVariantArity &self si:SumInfo k:long -> long {
        if (si.enumAt >= 0) { return gReg.variantAt(gReg.enumDef(si.enumAt), k).payloadCount; }
        return gReg.gVariantAt(gReg.templateDef(si.tmplAt), k).payloadCount;
    }
    sumVariantIndex &self si:SumInfo name:str -> long {
        for k in 0..self.sumVariantCount(si) {
            if (nameOf(self.sumVariantName(si, k)) == name) { return k; }
        }
        return NOT_FOUND;
    }

    // The type of one value a variant carries. A concrete sum type is registered as a struct too,
    // so its payload is an ordinary field; a template's is the field it declared, under whatever
    // the instance was requested with.
    sumPayloadType &self si:SumInfo variant:Sym i:long -> TypeRef {
        want: Sym = enumPayloadField(nameOf(variant), i);
        if (si.enumAt >= 0) {
            at: long = gReg.findStructSym(si.owner);
            if (at < 0) { return typeRefOf(Lit.Long); }
            d: StructDef = gReg.structDef(at);
            fi: long = gReg.findFieldSym(d, want);
            if (fi < 0) { return typeRefOf(Lit.Long); }
            f: FieldDef = gReg.fieldAt(d, fi);
            return TypeRef { base: f.kind, name: f.structName };
        }
        if (si.tmplAt < 0) { return typeRefOf(Lit.Long); }
        t: GTemplate = gReg.templateDef(si.tmplAt);
        for k in 0..t.fieldCount {
            g: GField = gReg.gFieldAt(t, k);
            if (g.name == want) { return self.sumSubst(si, t, g.kind); }
        }
        return typeRefOf(Lit.Long);
    }

    // A template's payload type under the arguments its instance was requested with. Inside the
    // template's own methods there are none, so a parameter stays what it is.
    sumSubst &self si:SumInfo t:GTemplate ty:TypeRef -> TypeRef {
        if (si.reqAt < 0 || ty.base != Lit.TypeVar) { return ty; }
        r: GRequest = gReg.requestAt(si.reqAt);
        k: long = 0;
        while (k < t.paramCount && k < r.argCount) {
            if (gReg.gParamAt(t, k) == ty.name) { return gReg.gArgAt(r, k); }
            k = k + 1;
        }
        return ty;
    }
}

methods Parser {
    // ─── top level ───────────────────────────────────────────────────────────

    // A declaration's visibility, if it is spelled. `local` is the default and means this file
    // only, not this module, because two files may share a module name and naming your file
    // after someone else's must not hand you their private declarations.
    parseVisibility &self -> Vis {
        if (self.eatWord("pub"))   { return Vis.Pub; }
        if (self.eatWord("pkg"))   { return Vis.Pkg; }
        if (self.eatWord("local")) { return Vis.Local; }
        return Vis.Local;
    }

    // `name: T;` / `name: T = v;` / `name: [T; N];` at the top level is a file global, not a
    // local. The colon is already consumed.
    parseGlobal &self name:Sym vis:Vis -> long {
        kind: Lit = Lit.Void;
        sname: Sym = NO_SYM;
        isArray: bool = false;
        count: long = 0;

        if (self.check(Tok.LeftSquare)) {
            self.advance();
            elem: TypeRef = self.parseTypeRef();
            if (self.eat(Tok.Semicolon)) {
                count = self.parseArrayLength();
                self.expect(Tok.RightSquare);
                isArray = true;
                kind = elem.base;
                sname = elem.name;
            } else {
                self.expect(Tok.RightSquare);
                self.err(stringOf("a global cannot be a slice\nnote: it would be a view of nothing\nhelp: declare an array: `NAME: [T; N]`"));
            }
        } else {
            t: TypeRef = self.parseTypeRef();
            kind = t.base;
            sname = t.name;
        }

        init: NodeId = NO_NODE;
        if (self.eat(Tok.Equals)) { init = self.parseExpr(); }
        // `X: [T; N] = [a, b, ...]`: the literal stays the initializer, typed as the element.
        if (init != NO_NODE && self.ast.expr(init).op == Op.ArrayLit) {
            self.arrayLitFor(init, isArray, count);
            e: Expr = self.ast.expr(init);
            e.kind = kind;
            e.structName = sname;
            self.ast.setExpr(init, e);
        }
        isVar: bool = self.varDecl;
        self.varDecl = false;

        // Named, and its file and package taken, BEFORE the `;` is consumed: consuming it reads
        // the next token, and when this global is the last thing in its file that token is the
        // next file's, whose `#file` marker has already moved the lexer on. Qualified after it,
        // a file's last global would belong to whichever module happened to follow it.
        q: Sym = self.qualify(nameOf(name));
        file: Sym = self.lx.currentFile;
        pkg: Sym = self.lx.currentPackage;
        // A global shares the expression namespace with nothing else, but it does share the name
        // with types: `Foo` as a value and `Foo` as a type read the same.
        if (gReg.findGlobalSym(q) >= 0) {
            self.err(format("redefinition of `{}`", nameOf(name)));
        }
        self.requireTypeNameFree(nameOf(name));
        self.expect(Tok.Semicolon);
        regAddGlobal(GlobalDef { name: q, kind: kind, structName: sname,
                                   isArray: isArray, count: count, visibility: vis,
                                   file: file, pkg: pkg,
                                   init: init, isVar: isVar });
        self.ast.decls.push(VarDeclNode { name: q, kind: kind, structName: sname,
                                          isArray: isArray, count: count, conv: Conv.None,
                                          isVariadic: false, elemKind: Lit.Void,
                                          elemStruct: NO_SYM, init: init });
        st: long = self.ast.addStmt(StmtKind.VarDecl, self.ast.decls.len() - 1);
        return st;
    }

    // An array literal where an array of `count` elements is declared: one element per slot.
    arrayLitFor &self init:NodeId isArray:bool count:long -> LitNode {
        ln: LitNode = LitNode { typeName: NO_SYM, firstInit: 0, initCount: 0, rest: NO_NODE };
        e: Expr = self.ast.expr(init);
        match e.payload { Lit(l) { ln = self.ast.lits.get(l); } _ { } }
        if (!isArray) {
            self.err(stringOf("an array literal can only initialize an array\nhelp: declare an array: `xs: [T; N] = [...]`"));
            return ln;
        }
        if (count >= 0 && ln.initCount != count) {
            self.err(format("wrong number of elements in array literal: expected {}, found {}\nnote: an array literal names every element",
                            count, ln.initCount));
        }
        return ln;
    }

    // ─── methods ─────────────────────────────────────────────────────────────

    // Every `methods X for T` this module wrote must name a trait. Without this check, one that
    // names nothing would declare a trait of its own in passing (`methods X for Drop` in a file
    // that included nothing, `Add` in a module that does not include `core`), and the
    // implementation would quietly do nothing.
    checkImplTraits &self -> void {
        for c in self.implChecks {
            if (self.abandonedName(c.trait)) { continue; }
            if (c.isType) {
                // `Result<long, long>` with no `Result` anywhere. Left alone it would stand as a
                // struct nobody declared, and the first thing to notice would be whatever read it
                // as one (a `match` saying it is not an enum).
                if (gReg.findTemplateSym(c.trait) >= 0 || gReg.declares(nameOf(c.trait))) { continue; }
                tb: str = lastComponentOf(nameOf(c.trait));
                failAtStr(nameOf(c.file), c.line, c.col,
                          format("cannot find type `{}` in this scope{}", tb, stdlibHint(tb)));
                continue;
            }
            if (c.trait == NO_SYM || gReg.findTraitSym(c.trait) >= 0) { continue; }
            bare: str = lastComponentOf(nameOf(c.trait));
            why: String;
            if (gReg.findTrait(bare) >= 0) {
                why = format("trait `{}` is declared below its implementation for `{}`\nnote: a `pub` trait must be declared above its implementations\nhelp: move the trait's declaration above this `methods` block",
                             bare, keepString(spellTypeName(nameOf(c.owner))));
            } else {
                why = format("cannot find trait `{}` in this scope{}", bare, stdlibHint(bare));
            }
            failAtStr(nameOf(c.file), c.line, c.col, why);
        }
        self.implChecks.clear();
    }

    // `methods T { ... }` and `methods T for Trait { ... }`.
    //
    // Each method becomes an ordinary top-level function named `T_method`, with the receiver as
    // its first parameter. Nothing after this point knows methods exist, which is what keeps the
    // call, the convention check and the lowering paths single.
    parseMethodsBlock &self -> long {
        if (self.check(Tok.LessThan)) { return self.parseBlanketMethods(); }
        tname: Token = self.expect(Tok.Id);
        return self.parseMethodsOf(tname);
    }

    // `methods<T: Integer> T for Hash { ... }`: one implementation for each scalar the category
    // holds, as if written out once per type. Without `for`, the methods are inherent ones, each
    // type's own. The block is read once per type, from the same text, with `T` standing for
    // that type (`blanketVar`), so each reading is exactly the hand-written
    // `methods long for Hash { ... }`, checked and named as one. The categories are the
    // compiler's own, so the set is closed and the expansion is all there is to it. No generic
    // body survives, and a hand-written implementation for one of the types is a duplicate, just
    // as it would be beside implementations written out by hand.
    parseBlanketMethods &self -> long {
        self.expect(Tok.LessThan);
        tv: Token = self.expect(Tok.Id);
        if (!self.eat(Tok.Colon)) {
            self.err(format("a blanket implementation must name its category of scalars\nhelp: write `methods<{}: Integer> {} for Trait`; the categories are `Integer`, `Signed`, `Unsigned` and `Float`",
                            nameOf(tv.text), nameOf(tv.text)));
        }
        cat: Token = self.expect(Tok.Id);
        kinds: Vec<Lit> = blanketScalars(nameOf(cat.text));
        if (kinds.len() == 0) {
            self.err(format("`{}` is not a category of scalars\nnote: a blanket implementation is over `Integer`, `Signed`, `Unsigned` or `Float`",
                            nameOf(cat.text)));
        }
        self.closeAngle();
        own: Token = self.expect(Tok.Id);
        if (own.text != tv.text) {
            self.err(format("the blanket implementation `methods<{}: {}> {}` must be for `{}` itself",
                            nameOf(tv.text), nameOf(cat.text), nameOf(own.text), nameOf(tv.text)));
        }
        // Each reading starts here: at `for` when the block implements a trait, at its `{` when its
        // methods are inherent (`methods<T: Integer> T { twice &self -> T {...} }`, every integer
        // type's own `twice`). Each reading is an ordinary `methods long ...` block.
        savedLx: Lexer = self.lx;
        savedCur: Token = self.cur;
        savedPeeked: Token = self.peeked;
        savedHas: bool = self.hasPeeked;
        savedCurPos: long = self.curPos;
        savedPeekPos: long = self.peekPos;
        first: long = NO_STMT;
        for k in kinds {
            self.lx = savedLx;
            self.cur = savedCur;
            self.peeked = savedPeeked;
            self.hasPeeked = savedHas;
            self.curPos = savedCurPos;
            self.peekPos = savedPeekPos;
            self.blanketVar = tv.text;
            self.blanketAs = intern(typeName(k));
            st: long = self.parseMethodsOf(tokenText(Tok.Id, self.blanketAs));
            if (first == NO_STMT) { first = st; } else { self.pending.push(st); }
        }
        self.blanketVar = NO_SYM;
        self.blanketAs = NO_SYM;
        return first;
    }

    // The rest of `methods X ...`, its type's name read.
    parseMethodsOf &self tname:Token -> long {
        // `methods long for Ord`: a scalar owns methods too, and its name belongs to no module:
        // qualifying it would name a type nobody declared, and every call site builds `long_cmp`
        // from the type's own spelling.
        owner: Sym = tname.text;
        if (namesScalar(nameOf(tname.text))) {
            if (!isImplableScalar(scalarNamed(nameOf(tname.text)))) {
                self.err(format("cannot write `methods {}`\nnote: `{}` is a shape, not a type with values to implement methods for",
                                nameOf(tname.text), nameOf(tname.text)));
            }
        } else {
            owner = self.resolveHere(nameOf(tname.text));
        }
        // `methods Vec<T: Copy>`, the parameters stay in scope for every method in the block: a
        // body may name `T` as freely as the struct's fields do, and each method carries the
        // block's bounds so monomorphization can decline an instance that does not meet them.
        bs: Vec<MethodBound>;
        names: Vec<Sym> = self.parseParamNamesInto(&bs);
        self.boundFirst = regAddBounds(bs);
        self.boundCount = bs.len();
        self.methodsHeaderKinds(owner, names);

        // `trait` is a keyword, so the trait's name cannot itself be one.
        tr: TraitRef = TraitRef { name: NO_SYM, firstArg: 0, argCount: 0 };
        if (self.eatWord("for")) {
            tr = self.parseTraitRef();
            // Whether the trait exists is asked once the module has been read, since it may be
            // declared below (`checkImplTraits`).
            self.implChecks.push(ImplCheck { trait: tr.name, owner: owner, line: self.lx.fileLine,
                                             col: self.lx.charNumber, file: self.lx.currentFile,
                                             isType: false });
            if (gReg.implementsTrait(owner, tr)) {
                self.err(format("`{}` already implements `{}`\nnote: a type implements a trait only once",
                                nameOf(owner), gReg.traitMangled(tr)));
            }
        }
        // A trait with arguments can be implemented more than once for the same type (`String`
        // is `Eq<str>` and `Eq<String>` both), and a file's own trait beside another file's of
        // the same spelling, so their methods carry the trait in their names (`implFnName`). A
        // flat one without arguments can only be implemented once, and keeps the plain name.
        // So does a flat one whose method names another trait's implementation for this type
        // already took (two `pub` traits sharing a method name: `Registry.flatCarries`). A flat
        // trait is declared above its implementations (`checkImplTraits` refuses one below), so
        // its methods are known here.
        self.implMangled = NO_SYM;
        carried: bool = false;
        if (tr.name != NO_SYM) { carried = gReg.flatCarries(owner, tr); }
        if (carried || traitCarriesName(tr)) { self.implMangled = intern(gReg.traitMangled(tr)); }
        self.expect(Tok.LeftCurly);

        implFns: Vec<Sym>;
        first: long = NO_STMT;
        self.inImpl = tr.name != NO_SYM;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            st: long = self.parseMethod(owner);
            // The block is one syntactic construct but many definitions. The first becomes this
            // statement; the rest are queued for the page to splice in after it.
            if (first == NO_STMT) { first = st; } else { self.pending.push(st); }
            implFns.push(self.ast.fns.get(self.ast.stmts.get(st).at).name);
        }
        self.expect(Tok.RightCurly);
        self.inImpl = false;
        self.clearTypeVars();
        self.leaveTemplate();
        self.boundCount = 0;

        self.implMangled = NO_SYM;
        if (tr.name != NO_SYM) { regAddImpl(owner, tr, implFns, carried); }
        // An empty block still stands as one statement: a marker naming its owner.
        if (first == NO_STMT) {
            self.ast.structDecls.push(owner);
            first = self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1);
        }
        return first;
    }

    // A methods block's header names the template's parameters it uses, which is what binds them
    // in its bodies; what each one IS comes from the template. So `methods Buf<T, N>` needs no
    // `N: long` (it may say so), a default belongs on the declaration, and a parameter the header
    // leaves out is still this instance's own wherever the template is named inside the block.
    methodsHeaderKinds &self owner:Sym names:Vec<Sym> -> void {
        tat: long = gReg.findTemplateSym(owner);
        for k in 0..names.len() {
            info: GParamInfo = self.tplParams.get(k);
            if (info.deflt.base != Lit.Void) {
                self.err(format("a default for `{}` belongs on the declaration of `{}`, not on a `methods` block",
                                nameOf(names.get(k)), nameOf(owner)));
            }
            isLen: bool = false;
            if (tat >= 0) {
                t: GTemplate = gReg.templateDef(tat);
                at: long = gReg.gParamIndex(t, names.get(k));
                isLen = at >= 0 && gReg.gParamIsLen(t, at);
            }
            if (info.isLen && !isLen) {
                self.err(format("`{}` is not a length parameter of `{}`", nameOf(names.get(k)), nameOf(owner)));
            }
            if (isLen && !info.isLen) { self.lenVars.push(names.get(k)); }
        }
        if (tat >= 0) { self.enterTemplate(owner); }
    }

    // One method: `name &self args -> Ret { }`, or `name args -> Ret { }` for a static one. The
    // receiver, when there is one, becomes the first parameter.
    parseMethod &self owner:Sym -> long {
        isUnsafe: bool = self.eatWord("unsafe");     // an unsafe method: its body is one trusted region
        mname: Token = self.expect(Tok.Id);
        // `E.x(...)` reads `x` as a variant when E has one, so a method of that name could only
        // be reached half the time: refused where it is declared.
        if (self.sumHasVariant(owner, mname.text)) {
            self.err(format("enum `{}` has a variant `{}`, so it cannot also have a method of that name",
                            nameOf(owner), nameOf(mname.text)));
        }
        // Named before the body moves the lexer on.
        under: Sym = owner;
        if (self.implMangled != NO_SYM) { under = methodName(owner, self.implMangled); }
        q: Sym = methodName(under, mname.text);
        file: Sym = self.lx.currentFile;
        pkg: Sym = self.lx.currentPackage;

        // `bind<A: ToSocketAddrs> a:A -> L`: a method with type parameters of its own, beside its
        // block's. It is a generic function (a template recorded under the method's name), over
        // its own parameters only; in a generic block, each instance's copy of it is one again.
        ownParams: Vec<Sym>;
        ownBs: Vec<MethodBound>;
        ownInfos: Vec<GParamInfo>;
        varsBefore: long = self.typeVars.len();
        lensBefore: long = self.lenVars.len();
        if (self.check(Tok.LessThan)) {
            if (self.inImpl) {
                self.err(format("trait method `{}` cannot have type parameters of its own\nhelp: declare it in a plain `methods` block",
                                nameOf(mname.text)));
            }
            ownParams = self.parseParamNamesInto(&ownBs);
            ownInfos.extend(self.tplParams);
            for k1 in 0..ownParams.len() {
                for j1 in 0..varsBefore {
                    if (self.typeVars.get(j1) == ownParams.get(k1)) {
                        self.err(format("`{}` is already a type parameter of the `methods` block", nameOf(ownParams.get(k1))));
                    }
                }
            }
        }
        self.pushScope();

        params: Vec<long>;
        lent: bool = self.eat(Tok.Ampersand);
        if (lent || self.word("self")) {
            if (!self.eatWord("self")) { self.err(format("expected `self`, found {}", describeTok(self.cur))); }
            // `&self` lends the receiver; a bare `self` takes it, which is how a method that
            // consumes its value (`unwrap`, `pop`) says so.
            kind: Lit = Lit.Struct;
            conv: Conv = Conv.Sink;
            if (lent) { kind = Lit.Ref; conv = Conv.Inout; }
            renamed: Sym = self.declareLocal(intern("self"), kind, owner);
            self.ast.decls.push(VarDeclNode { name: renamed, kind: kind, structName: owner,
                                              isArray: false, count: 0, conv: conv,
                                              isVariadic: false, elemKind: Lit.Void,
                                              elemStruct: NO_SYM, init: NO_NODE });
            params.push(self.ast.decls.len() - 1);
        }

        rest: Vec<long> = self.parseParams();
        params.extend(rest);

        self.expect(Tok.Arrow);
        ret: TypeRef = self.parseRetType();
        mattrs: long = 0;
        if (self.retNever) { mattrs = FN_NEVER; }
        self.fnDepth = self.fnDepth + 1;      // inside a body a declaration is a local, not a global
        was: Sym = gReg.deferIn;
        wasPlain: bool = self.plainBody;
        self.plainBody = !gReg.isGenericSym(owner) && self.typeVars.len() == 0;
        if (!gReg.isGenericSym(owner) && self.typeVars.len() == 0 && isUpstreamPkg(pkg)) { gReg.deferIn = file; }
        wasRet: TypeRef = self.retTy;
        wasRetOk: bool = self.retOk;
        self.retTy = ret;
        self.retOk = true;
        if (isUnsafe) { self.unsafeDepth = self.unsafeDepth + 1; }
        body: long = self.parseBlock();
        if (isUnsafe) { self.unsafeDepth = self.unsafeDepth - 1; }
        self.retTy = wasRet;
        self.retOk = wasRetOk;
        gReg.deferIn = was;
        self.plainBody = wasPlain;
        self.fnDepth = self.fnDepth - 1;
        self.popScope();

        firstArg: long = self.ast.addParams(params);
        // A block's bounds travel on its methods (an instance that misses one has no such method);
        // a generic method's own go on it when its block has none to carry, as a generic
        // function's do, and on its template either way: an instance's copy takes them from there.
        fb: long = self.boundFirst;
        fc: long = self.boundCount;
        ownerGeneric: bool = gReg.isGenericSym(owner);
        if (ownParams.len() > 0 && !ownerGeneric) { fb = regAddBounds(ownBs); fc = ownBs.len(); }
        self.ast.fns.push(FnNode { name: q,
                                   returnKind: ret.base, returnStruct: ret.name,
                                   visibility: Vis.Pub,
                                   file: file, pkg: pkg,
                                   isUnsafe: isUnsafe,
                                   isTemplate: ownerGeneric || ownParams.len() > 0, inferReturn: false,
                                   firstBound: fb, boundCount: fc,
                                   firstArg: firstArg, argCount: params.len(), body: body, attrs: mattrs });
        st: long = self.ast.addStmt(StmtKind.FunctionDef, self.ast.fns.len() - 1);
        if (ownParams.len() > 0) {
            if (body < 0) {
                self.err(format("generic method `{}` has no body\nnote: a generic method has no symbol to link against, so a declaration without a body cannot take type parameters",
                                nameOf(mname.text)));
            }
            heldBs: Vec<MethodBound>;
            heldBs.extend(self.tplBounds);
            self.tplBounds = ownBs;
            self.tplParams = ownInfos;
            noFields: Vec<GField>;
            self.recordTemplate(q, ownParams, noFields, false);
            self.tplBounds = heldBs;
            while (self.typeVars.len() > varsBefore) { self.typeVars.pop(); }
            while (self.lenVars.len() > lensBefore) { self.lenVars.pop(); }
        }
        return st;
    }
}

methods Parser {
    // ─── traits ──────────────────────────────────────────────────────────────

    // `trait Name { method &self args -> Ret; }`: a named set of method signatures, which is a
    // contract and nothing else: there are no bodies here and no inheritance. A type answers it
    // with `methods T for Name { }`.
    parseTraitDecl &self -> long {
        name: Token = self.expect(Tok.Id);
        self.declName = name.text;
        // A `pub` (or `pkg`) trait's name is flat: one program-wide name, which a repeat that says
        // the same thing re-declares. A trait declared without either belongs to its file, as a
        // struct does (`geo::Shape`), so two files may each have their own and a program's
        // `trait Ord` is not the standard library's. The core traits are the exception: the
        // compiler looks them up by bare name (`Drop`, `Copy`, `Default`), so writing one
        // re-declares core's whatever the visibility.
        q: Sym = name.text;
        owned: bool = self.vis == Vis.Local && !isCoreTraitName(nameOf(name.text));
        if (owned) { q = self.qualify(nameOf(name.text)); }
        // Only a fresh trait has to claim the name; a repeat already owns it.
        already: long = gReg.findTraitSym(q);
        if (already < 0) {
            // A file's own trait may share its spelling with a `pub` one it can see, and shadows
            // it here as a file's own struct would.
            if (owned) { self.requireOwnTypeNameFree(nameOf(name.text)); }
            else { self.requireTypeNameFree(nameOf(name.text)); }
        }

        // `trait Iter<T>`: the parameters are recorded so the trait can be stamped out per
        // instantiation, exactly as a generic struct is.
        params: Vec<TypeRef> = self.parseTypeParams();
        // In scope for the signatures that follow: `-> R` has to come back as the type variable
        // R, not as a type named `core::R` that nobody declared. Stamping substitutes by that
        // name, and a qualified one would never match: `Fn(long) -> long` would keep `R` as its
        // return, and every call through one would be lowered as if it returned a struct.
        for k in 0..params.len() { self.typeVars.push(params.get(k).name); }
        // `trait Encode derive deriveEncode { ... }`: a type with no `methods X for Encode` gets
        // one written by that macro, the first time the program needs it (see the checker's
        // `ensureImpl`). Kept as written; it resolves in this file's module when it runs, which
        // is what lets the macro be declared below the trait that names it.
        tfile: Sym = self.lx.currentFile;     // before the body moves the lexer on
        deriveBy: Sym = NO_SYM;
        if (self.word("derive") && self.peekNext().kind == Tok.Id) {
            self.advance();
            deriveBy = self.expect(Tok.Id).text;
            if (params.len() > 0) {
                self.err(format("generic trait `{}` cannot name a derive macro\nnote: only a trait without type parameters can name one",
                                nameOf(name.text)));
            }
        }
        self.expect(Tok.LeftCurly);

        sigs: Vec<TraitMethodSig>;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            mname: Token = self.expect(Tok.Id);
            isStatic: bool = true;
            lentSelf: bool = false;
            if (self.eat(Tok.Ampersand)) { self.eatWord("self"); isStatic = false; lentSelf = true; }
            else if (self.eatWord("self")) { isStatic = false; }   // by value, not lent
            self.pushScope();
            ps: Vec<long> = self.parseParamList(true);
            self.popScope();
            self.expect(Tok.Arrow);
            // `-> Self` names the implementing type, which a trait cannot know. Kept as that
            // one word rather than resolved: resolving it would qualify it with whichever module
            // the trait was written in, so `core`'s `Clone` and a test file's identical
            // re-declaration of it would stop comparing equal, and the repeat would read as a
            // conflict.
            ret: TypeRef = TypeRef { base: Lit.Struct, name: intern("Self") };
            if (self.word("Self")) { self.advance(); }
            else { ret = self.parseTypeRef(); }
            self.eat(Tok.Semicolon);
            // The parameters are kept, not just counted: a trait says how it hands each one over
            // (`v: sink T`) as part of the contract, and for a method reached through a trait
            // object that signature is the only place the convention is written. There is no
            // function node at the call site to read it back from.
            sigs.push(TraitMethodSig { name: mname.text,
                                       returnKind: ret.base, returnName: ret.name,
                                       firstParam: self.ast.addParams(ps), paramCount: ps.len(),
                                       isStatic: isStatic, lentSelf: lentSelf });
        }
        self.expect(Tok.RightCurly);
        self.clearTypeVars();
        // A repeat that names no derive keeps the first one's; one that names another is a
        // different trait, and refused with the rest below.
        if (deriveBy != NO_SYM) {
            had: Sym = gReg.deriveMacroOf(q);
            if (already >= 0 && had != NO_SYM && had != deriveBy) {
                self.err(format("trait `{}` is already declared with derive macro `{}`", nameOf(name.text), nameOf(had)));
            }
            if (had == NO_SYM) { regNoteDerive(q, deriveBy, tfile); }
        }

        // A repeat keeps the first declaration, which is what makes re-declaring a core trait
        // instead of including <core> work; a repeat that says something else is refused.
        if (already >= 0) {
            if (!gReg.sameTrait(gReg.traitDef(already), sigs, params.len())) {
                self.err(format("trait `{}` is already declared with different methods",
                                nameOf(name.text)));
            }
        } else {
            regDeclareTrait(q, sigs, params, &self.ast);
        }

        self.ast.structDecls.push(q);
        st: long = self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1);
        return st;
    }

    // `<T, U: Bound>` if it is there, otherwise nothing. The bounds are parsed and discarded here;
    // enforcing them is monomorphization's job, and it reads them from the template.
    parseTypeParams &self -> Vec<TypeRef> {
        out: Vec<TypeRef>;
        if (!self.check(Tok.LessThan)) { return out; }
        self.advance();
        while (!self.check(Tok.GreaterThan) && !self.check(Tok.FileEnd)) {
            pname: Token = self.expect(Tok.Id);
            out.push(TypeRef { base: Lit.TypeVar, name: pname.text });
            if (self.eat(Tok.Colon)) {
                b: Token = self.expect(Tok.Id);            // the first bound
                if (namesScalar(nameOf(b.text))) {
                    self.err(format("a trait takes only type parameters\nnote: `{}: {}` would declare a length parameter",
                                    nameOf(pname.text), nameOf(b.text)));
                }
                while (self.eat(Tok.Plus)) { self.expect(Tok.Id); }
            }
            self.eat(Tok.Comma);
        }
        self.expect(Tok.GreaterThan);
        return out;
    }

    // ─── type alias ──────────────────────────────────────────────────────────

    // `type Name = Existing;`. One name for another, resolved once and interchangeable after.
    parseTypeAlias &self -> long {
        name: Token = self.expect(Tok.Id);
        self.declName = name.text;
        self.requireTypeNameFree(nameOf(name.text));
        self.expect(Tok.Equals);
        if (self.word("distinct") && self.peekNext().kind != Tok.Semicolon) {
            self.advance();
            return self.parseDistinct(name);
        }
        target: TypeRef = self.parseTypeRef();
        // Before the `;`, for the reason `parseGlobal` gives: reading past it may already be
        // reading the next file.
        q: Sym = self.qualify(nameOf(name.text));
        file: Sym = self.lx.currentFile;
        pkg: Sym = self.lx.currentPackage;
        self.expect(Tok.Semicolon);
        // `requireTypeNameFree` above asks about this module's own names. A `pub` alias is not
        // this module's: it goes into the one flat namespace every module reads, so claiming a
        // name another module has already published there is a collision wherever it was written.
        // Declared without `pub` it is this file's own name and shadows theirs, which is what
        // `priv_alias.k` does.
        if (self.vis == Vis.Pub) {
            clash: Sym = gReg.otherPubAlias(nameOf(name.text), q);
            if (clash != NO_SYM) {
                self.err(format("the type name `{}` is already taken by the `pub` type alias `{}`\nhelp: drop the `pub` to make this alias this file's own",
                                nameOf(name.text), nameOf(clash)));
            }
        }
        regAddAlias(AliasDef { name: q, target: target, visibility: self.vis,
                                 file: file, pkg: pkg });
        self.ast.structDecls.push(q);
        st: long = self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1);
        return st;
    }

    // `type Meters = distinct long;`: a type of its own with the base's representation. It is
    // registered as what it is underneath, a named scalar (an enum with no variants over the
    // base's integer, which is how the compiler's own `Sym` is a type at no cost), and marked
    // distinct, which is what withholds the base's freedoms: it converts only by `as`, and has an
    // operator only where it implements the operator's trait. Its methods and impls are its own.
    // The base is an integer, a `char`, a `bool`, or a named scalar (a backed enum, another
    // distinct type); an aggregate base is refused rather than half-supported.
    parseDistinct &self name:Token -> long {
        base: TypeRef = self.parseTypeRef();
        backing: Lit = base.base;
        if (base.base == Lit.Struct && namedScalar(base.base, base.name)) { backing = namedScalarBacking(base.name); }
        else if (!(isInteger(base.base) || base.base == Lit.Char || base.base == Lit.Bool)) {
            self.err(format("cannot make a distinct type over `{}`\nnote: the base must be an integer, a `char` or a `bool`, or a type that is one\nnote: a distinct type over an aggregate is not supported yet\nhelp: wrap it in a struct",
                            typeMangleName(base.base, base.name)));
        }
        q: Sym = self.qualify(nameOf(name.text));
        // `with Add, Sub, Eq, Ord`: the base's operators, opted into by naming their traits.
        traits: Vec<Sym>;
        if (self.word("with") && !self.namedHere()) {
            self.advance();
            loop {
                t: Token = self.expect(Tok.Id);
                if (distinctImpl(nameOf(t.text), "T", "long").len == 0) {
                    self.err(format("a distinct type cannot take `{}` with `with`\nnote: `with` takes the base's operators by their traits: `Add`, `Sub`, `Mul`, `Div`, `Rem`, `BitAnd`, `BitOr`, `BitXor`, `Shl`, `Shr`, `Not`, `Eq`, `Ord` or `Hash`",
                                    nameOf(t.text)));
                }
                if (self.symSeen(traits, t.text)) { self.err(format("duplicate trait `{}` in `with`", nameOf(t.text))); }
                traits.push(t.text);
                if (!self.eat(Tok.Comma)) { break; }
            }
            if (self.fnDepth > 0) { self.err(stringOf("a distinct type with operators must be declared at the top level")); }
        }
        self.expect(Tok.Semicolon);
        none: Vec<VariantDef>;
        regAddEnum(q, backing, none, false);
        regAddDistinct(q, base);
        self.ast.structDecls.push(q);
        st: long = self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1);
        if (traits.len() == 0) { return st; }
        // Each implementation written out as source and read here, as a person would write it:
        // the base's operation between the two values converted with `as`, which costs nothing
        // (a distinct type is its base), so each inlines to the plain instruction.
        bs: str = typeName(base.base);
        if (base.base == Lit.Struct) { bs = lastComponentOf(nameOf(base.name)); }
        text: String;
        for t in traits { text.pushStr(distinctImpl(nameOf(t), nameOf(name.text), bs)); }
        self.parseSynthetic(keepString(text));
        return st;
    }

    // Top-level declarations written by the compiler, read where the declaration that asked for
    // them stands (its file, package and line), and put on the page after it (`pending`).
    //
    // The module's own cursor is kept in the parser rather than here, so that an error in the
    // text can put it back (`rewindTo`): this frame is gone by then.
    parseSynthetic &self text:str -> void {
        self.synthSaved.push(Cursor { lx: self.lx, cur: self.cur, peeked: self.peeked, hasPeeked: self.hasPeeked,
                                      curPos: self.curPos, peekPos: self.peekPos });
        l: Lexer = self.lx;
        l.src = text;
        l.pos = 0;
        l.afterDot = false;
        self.lx = l;
        self.hasPeeked = false;
        self.advance();
        while (!self.check(Tok.FileEnd)) { self.pending.push(self.parseStatement()); }
        c: Cursor = self.synthSaved.pop();
        self.lx = c.lx;
        self.cur = c.cur;
        self.peeked = c.peeked;
        self.hasPeeked = c.hasPeeked;
        self.curPos = c.curPos;
        self.peekPos = c.peekPos;
    }

    // ─── with ────────────────────────────────────────────────────────────────

    // `with x { }`: a scoped wrapper. The middle end desugars it: enter `x` (its `hold()` returns
    // a guard), rewrite reads of `x` to the guard's `get()` and writes to its `set()`, and let the
    // guard drop at the block's end.
    parseWith &self -> long {
        name: Token = self.expect(Tok.Id);
        bound: Sym = self.lookupLocal(name.text);
        if (bound == NO_SYM) { bound = self.qualify(nameOf(name.text)); }
        body: long = self.parseBlock();
        self.ast.withs.push(WithNode { name: bound, body: body });
        st: long = self.ast.addStmt(StmtKind.With, self.ast.withs.len() - 1);
        return st;
    }
}

methods Parser {
    // ─── inline assembly ─────────────────────────────────────────────────────

    // `asm { in <reg> <expr>; "literal"; out <var> <reg>; }`. The pieces keep their source order,
    // because the literal lines are emitted verbatim between the register moves.
    parseAsmBlock &self -> long {
        // `asm -> never { ... }`: the block does not come back.
        noReturn: bool = false;
        if (self.eat(Tok.Arrow)) {
            if (!self.eatWord("never")) { self.err(format("expected `never`, found {}\nnote: `asm -> never {{ ... }}` is the only result an `asm` block declares", describeTok(self.cur))); }
            noReturn = true;
        }
        self.expect(Tok.LeftCurly);
        pieces: Vec<AsmPiece>;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            if (self.check(Tok.StringLiteral)) {
                t: Token = self.advance();
                pieces.push(AsmPiece { kind: AsmKind.Text, reg: NO_SYM, name: NO_SYM,
                                       value: NO_NODE, text: unquoted(t.text) });
                self.eat(Tok.Semicolon);
            } else if (self.eatWord("in")) {
                reg: Token = self.expect(Tok.Id);
                v: NodeId = self.parseExpr();
                self.expect(Tok.Semicolon);
                pieces.push(AsmPiece { kind: AsmKind.In, reg: reg.text, name: NO_SYM,
                                       value: v, text: NO_SYM });
            } else if (self.eatWord("out")) {
                name: Token = self.expect(Tok.Id);
                reg: Token = self.expect(Tok.Id);
                self.expect(Tok.Semicolon);
                bound: Sym = self.lookupLocal(name.text);
                if (bound == NO_SYM) { bound = name.text; }
                pieces.push(AsmPiece { kind: AsmKind.Out, reg: reg.text, name: bound,
                                       value: NO_NODE, text: NO_SYM });
            } else {
                self.err(format("expected `in`, `out` or a string literal in an `asm` block, found {}", describeTok(self.cur)));
            }
        }
        self.expect(Tok.RightCurly);

        first: long = self.ast.asmPieces.len();
        self.ast.asmPieces.extend(pieces);
        self.ast.asms.push(AsmNode { firstPiece: first, pieceCount: pieces.len(), noReturn: noReturn });
        return self.ast.addStmt(StmtKind.Asm, self.ast.asms.len() - 1);
    }

    // ─── unsafe ──────────────────────────────────────────────────────────────

    // `unsafe` introduces either a trusted block or an unsafe function, and which one is decided
    // by what follows: a `{` is the block, anything else is a definition whose whole body is one
    // trusted region and whose callers must themselves be inside one.
    parseUnsafe &self -> long {
        if (self.check(Tok.LeftCurly)) {
            self.unsafeDepth = self.unsafeDepth + 1;
            b: long = self.parseBlock();
            self.unsafeDepth = self.unsafeDepth - 1;
            self.ast.blockStmts.push(BlockStmtNode { body: b });
            return self.ast.addStmt(StmtKind.Unsafe, self.ast.blockStmts.len() - 1);
        }
        // `pub unsafe builtin syscall ...`
        if (self.fnDepth == 0 && self.word("builtin") && !self.namedHere() && self.peekNext().kind == Tok.Id) {
            self.advance();
            self.fnAttrs = FN_BUILTIN_DECL;
        }
        self.unsafeDepth = self.unsafeDepth + 1;
        st: long = self.parseStatement();
        self.unsafeDepth = self.unsafeDepth - 1;
        // Mark the definition it produced. Anything else after `unsafe` is a mistake.
        s: Stmt = self.ast.stmts.get(st);
        if (s.kind != StmtKind.FunctionDef) {
            self.err(stringOf("`unsafe` must be followed by a function definition or a `{ ... }` block"));
        }
        f: FnNode = self.ast.fns.get(s.at);
        f.isUnsafe = true;
        self.ast.fns.set(s.at, f);
        return st;
    }
}

methods Parser {
    // ─── generics ────────────────────────────────────────────────────────────

    // The names a `<T, U: Bound>` list binds, when the bounds do not matter to the caller.
    parseParamNames &self -> Vec<Sym> {
        bs: Vec<MethodBound>;
        return self.parseParamNamesInto(&bs);
    }

    // The names, and every `T: Trait` alongside them. A bound is not decoration: a methods block
    // carrying one applies only to the instances that meet it, which is what keeps `W.new()` out
    // of `BufWriter<Write>`: a trait object is not `Default`.
    //
    // A parameter is a type unless it says otherwise. `N: long` makes it a length: it stands where
    // an array's length does (`[u8; N]`) and, in a body, for its value. It is marked rather than
    // inferred from how it is used, because a use can be anywhere (only in a function's return
    // type, or only in a field below) and the parser has to know what `N` is the moment it meets it.
    // `= default` gives what a use that leaves it out means (`<W, N: long = 4096>`, `<T, A = Heap>`).
    // What the header said of each is left in `tplParams` for the caller that records it.
    parseParamNamesInto &self inout bs:Vec<MethodBound> -> Vec<Sym> {
        out: Vec<Sym>;
        self.tplParams.clear();
        if (!self.check(Tok.LessThan)) { return out; }
        self.advance();
        defaulted: bool = false;
        while (!self.atCloseAngle() && !self.check(Tok.FileEnd)) {
            pname: Token = self.expect(Tok.Id);
            out.push(pname.text);
            // In scope from the moment it is named, because its own bound may mention it and a
            // later parameter's certainly may: `count<T, I: Iter<T>>` reads `T` inside I's bound,
            // and a `T` not yet bound resolves as the name of a struct nobody declared. This is
            // the only place they are bound. A caller must not bind the returned list again: the
            // scope is also read as the ordered list a closure template needs, and a second copy
            // would show up in it.
            self.typeVars.push(pname.text);
            info: GParamInfo = GParamInfo { isLen: false, deflt: typeRefOf(Lit.Void) };
            if (self.eat(Tok.Colon)) {
                // A scalar is never a trait, so `N: long` cannot be read as a bound.
                if (self.check(Tok.Id) && namesScalar(nameOf(self.cur.text))) {
                    sc: Token = self.advance();
                    if (nameOf(sc.text) != "long") {
                        self.err(format("a length parameter must be a `long`\nhelp: write `{}: long`", nameOf(pname.text)));
                    }
                    if (self.check(Tok.Plus)) {
                        self.err(format("length parameter `{}` cannot take a trait bound", nameOf(pname.text)));
                    }
                    info = GParamInfo { isLen: true, deflt: info.deflt };
                    self.lenVars.push(pname.text);
                } else {
                    bs.push(MethodBound { param: out.len() - 1, trait: self.parseTraitRef() });
                    while (self.eat(Tok.Plus)) {
                        bs.push(MethodBound { param: out.len() - 1, trait: self.parseTraitRef() });
                    }
                }
            }
            if (self.eat(Tok.Equals)) {
                // A default is a fact about the template, written where it is declared. One that
                // named another parameter would need that parameter's argument to mean anything,
                // and a use that leaves this one out is read before any instance exists.
                uses: long = self.typeVarUses;
                d: TypeRef = typeRefOf(Lit.Void);
                if (info.isLen) {
                    d = lengthArg(self.parseAngleLength());
                } else {
                    d = self.parseTypeRef();
                }
                if (self.typeVarUses != uses) {
                    self.err(format("the default for `{}` cannot name a parameter of the template\nnote: a default is a fixed type or length",
                                    nameOf(pname.text)));
                }
                info = GParamInfo { isLen: info.isLen, deflt: d };
                defaulted = true;
            } else if (defaulted) {
                // A use gives its arguments in order, so only a trailing run can be left out.
                self.err(format("`{}` needs a default, because it follows a parameter with one",
                                nameOf(pname.text)));
            }
            self.tplParams.push(info);
            self.eat(Tok.Comma);
        }
        self.closeAngle();
        return out;
    }

    // Is `name` a length parameter in scope?
    isLenVar &self name:Sym -> bool {
        for i in 0..self.lenVars.len() {
            if (self.lenVars.get(i) == name) { return true; }
        }
        return false;
    }

    // Each of `params` as a template records it: a length if it is one in scope, with no default.
    // For a template the parser makes itself (a closure's capture struct) over the parameters of
    // the function it is written in.
    paramInfosOf &self params:Vec<Sym> -> Vec<GParamInfo> {
        out: Vec<GParamInfo>;
        for k in 0..params.len() {
            out.push(GParamInfo { isLen: self.isLenVar(params.get(k)), deflt: typeRefOf(Lit.Void) });
        }
        return out;
    }

    // The parameters `base` declares, so `Name<...>` can be held to them: this template's own
    // while its declaration is being read (it is recorded only at the `}`), otherwise the
    // registry's run. Not `known` when the template has not been declared yet. A view, so asking
    // copies nothing: it is asked at every generic use the parser reads.
    tplRef &self base:Sym -> TplRef {
        if (base != NO_SYM && base == self.selfTpl) {
            return TplRef { known: true, own: true, first: 0, count: self.selfParams.len() };
        }
        at: long = gReg.findTemplateSym(base);
        if (at < 0) { return TplRef { known: false, own: false, first: 0, count: 0 }; }
        t: GTemplate = gReg.templateDef(at);
        return TplRef { known: true, own: false, first: t.firstParam, count: t.paramCount };
    }
    tplName &self r:TplRef k:long -> Sym {
        if (r.own) { return self.selfParams.get(k); }
        return gReg.gParams.get(r.first + k);
    }
    tplInfo &self r:TplRef k:long -> GParamInfo {
        if (r.own) { return self.selfInfo.get(k); }
        return gReg.gParamInfo.get(r.first + k);
    }

    // Reading a declaration or a methods block of the template `q`: inside it, a use of `q` that
    // leaves out a parameter means this instance's own.
    enterTemplate &self q:Sym -> void {
        self.leaveTemplate();
        r: TplRef = self.tplRef(q);
        if (!r.known) { return; }
        for k in 0..r.count {
            self.selfParams.push(self.tplName(r, k));
            self.selfInfo.push(self.tplInfo(r, k));
        }
        self.selfTpl = q;
    }
    // The same, for a template whose header was just read and which is recorded only at its `}`.
    beginOwnTemplate &self q:Sym params:Vec<Sym> -> void {
        self.selfTpl = q;
        self.selfParams.clear();
        self.selfParams.extend(params);
        self.selfInfo.clear();
        self.selfInfo.extend(self.tplParams);
    }
    leaveTemplate &self -> void {
        self.selfTpl = NO_SYM;
        self.selfParams.clear();
        self.selfInfo.clear();
    }

    // ─── lengths ─────────────────────────────────────────────────────────────

    // `[T; n]`'s length: a constant (an integer expression over literals and constant globals,
    // `PATH_MAX + 1`) or, inside a template, one of its length parameters standing alone. A
    // parameter comes back as `countOfParam`, which each instance replaces with its value.
    parseArrayLength &self -> long {
        if (self.check(Tok.Id) && self.isTypeVar(self.cur.text) && self.peekNext().kind == Tok.RightSquare) {
            n: Token = self.advance();
            if (!self.isLenVar(n.text)) {
                self.err(format("`{}` is a type parameter, not a length\nhelp: declare a length parameter as `{}: long`",
                                nameOf(n.text), nameOf(n.text)));
            }
            self.typeVarUses = self.typeVarUses + 1;
            return countOfParam(n.text);
        }
        return self.parseLengthValue();
    }

    // A length inside `<...>`, where `>` closes the list and cannot be read as an operator: an
    // integer literal or a constant global's name. A length that needs arithmetic is declared as a
    // constant first (`BIG: long = 64 * 1024;`), which is also what names it for a reader.
    parseAngleLength &self -> long {
        neg: bool = self.eat(Tok.Dash);
        v: long = 0;
        if (self.check(Tok.IntLiteral) || self.check(Tok.LongLiteral)) {
            v = self.advance().num;
        } else if (self.check(Tok.Id)) {
            name: Token = self.advance();
            written: str = nameOf(name.text);
            if (self.check(Tok.ColonColon)) { written = nameOf(self.qualifiedFrom(name)); }
            if (self.isTypeVar(name.text)) {
                self.err(format("a default cannot name template parameter `{}`\nnote: a default has to be a fixed length", written));
            }
            g: long = self.globalNamed(written, self.currentModule());
            if (g < 0) {
                self.err(format("`{}` is not a constant\nnote: a length is an integer literal, a constant global, or a length parameter",
                                written));
            }
            v = self.constGlobalValueIn(g, written, 0);
        } else {
            self.err(format("expected a length, found {}", describeTok(self.cur)));
        }
        if (neg) { v = -v; }
        if (v < 0) { self.err(format("a length cannot be negative, but this one is `{}`", v)); }
        return v;
    }

    // A length that has to be known here: an integer constant expression, never negative.
    parseLengthValue &self -> long {
        e: NodeId = self.parseExpr();
        v: long = self.foldConst(e, self.currentModule(), 0);
        if (v < 0) { self.err(format("a length cannot be negative, but this one is `{}`", v)); }
        return v;
    }

    // The value of an integer constant expression, as the parser read it, or an error saying why
    // it is not one. `here` is the module its names resolve in: the one being read, or, inside a
    // constant global's initializer, that global's.
    foldConst &self e:NodeId here:str depth:long -> long {
        if (depth > 64) { self.err(stringOf("a constant length refers to itself")); }
        x: Expr = self.ast.expr(e);
        p: Payload = x.payload;
        if (x.op == Op.Literal) {
            match p { Num(v) { if (isInteger(x.kind)) { return v; } } _ { } }
        }
        if (x.op == Op.Lvalue) {
            match p {
                Name(n) {
                    if (self.isLenVar(n)) {
                        self.err(format("length parameter `{}` cannot be used inside an expression\nnote: it stands alone as a length, as in `[T; {}]`",
                                        nameOf(n), nameOf(n)));
                    }
                    if (self.isTypeVar(n)) {
                        self.err(format("`{}` is a type parameter, not a length", nameOf(n)));
                    }
                    if (depth == 0 && self.bindingOf(n).renamed != NO_SYM) {
                        self.err(format("`{}` is a variable, not a constant\nnote: a length has to be a compile-time constant",
                                        nameOf(n)));
                    }
                    g: long = self.globalNamed(nameOf(n), here);
                    if (g < 0) {
                        self.err(format("`{}` is not a constant\nnote: a length is an integer literal, a constant global, or a length parameter",
                                        nameOf(n)));
                    }
                    return self.constGlobalValueIn(g, nameOf(n), depth);
                }
                _ { }
            }
        }
        if (x.op == Op.Cast && isInteger(x.kind)) {
            match p { Sub(v) { return self.foldConst(v, here, depth + 1); } _ { } }
        }
        if (x.op == Op.BitwiseNot) {
            match p { Sub(v) { return ~self.foldConst(v, here, depth + 1); } _ { } }
        }
        if (x.left != NO_NODE && x.right != NO_NODE) {
            if (x.op == Op.Addition || x.op == Op.Subtraction || x.op == Op.Multiplication
                || x.op == Op.Division || x.op == Op.Modulus || x.op == Op.BitwiseAnd
                || x.op == Op.BitwiseOr || x.op == Op.BitwiseXor || x.op == Op.ShiftLeft
                || x.op == Op.ShiftRight) {
                l: long = self.foldConst(x.left, here, depth + 1);
                r: long = self.foldConst(x.right, here, depth + 1);
                if (x.op == Op.Addition) { return l + r; }
                if (x.op == Op.Subtraction) { return l - r; }
                if (x.op == Op.Multiplication) { return l * r; }
                if (x.op == Op.BitwiseAnd) { return l & r; }
                if (x.op == Op.BitwiseOr) { return l | r; }
                if (x.op == Op.BitwiseXor) { return l ^ r; }
                if (x.op == Op.ShiftLeft) { return l << r; }
                if (x.op == Op.ShiftRight) { return l >> r; }
                if (r == 0) { self.err(stringOf("a constant length divides by zero")); }
                if (x.op == Op.Division) { return l / r; }
                return l % r;
            }
        }
        self.err(stringOf("a length has to be a compile-time constant\nnote: a constant is an integer literal, a constant global, arithmetic over those, or a length parameter"));
        return 0;
    }

    // The global a name means, read from `here`, or -1: a constant's for a length, and any
    // global's for `for x in G`'s element type. In the order a name resolves everywhere: `mod::X`
    // as written, then this module's own, then the one module this one can reach that declares it
    // (two is ambiguous, as for a type). Only its type is read here; the checker resolves the use.
    globalNamed &self spelled:str here:str -> long {
        if (lastComponentOf(spelled).len != spelled.len) { return gReg.findGlobal(spelled); }
        own: long = gReg.findGlobalSym(qualifiedName(here, spelled));
        if (own >= 0) { return own; }
        found: long = NOT_FOUND;
        for i in 0..gReg.globalCount() {
            q: str = nameOf(gReg.globalDef(i).name);
            if (q.len > spelled.len && lastComponentOf(q) == spelled) {
                m: str = strSlice(q, 0, q.len - spelled.len - 2);
                if (gImports.isEmpty() || gImports.canReach(here, m)) {
                    if (found >= 0) {
                        self.err(format("`{}` is ambiguous\nnote: it could be `{}` or `{}`\nhelp: write which one, as `{}`",
                                        spelled, nameOf(gReg.globalDef(found).name), q,
                                        nameOf(gReg.globalDef(found).name)));
                    }
                    found = i;
                }
            }
        }
        return found;
    }

    // A constant global's value, as a length: it is immutable, an integer, visible from here, and
    // initialized by a constant expression.
    constGlobalValue &self g:long spelled:str -> long {
        v: long = self.constGlobalValueIn(g, spelled, 0);
        if (v < 0) { self.err(format("a length cannot be negative, but `{}` is `{}`", spelled, v)); }
        return v;
    }
    constGlobalValueIn &self g:long spelled:str depth:long -> long {
        d: GlobalDef = gReg.globalDef(g);
        if (d.isVar) {
            self.err(format("`{}` is a `var`, so its value is not fixed\nnote: a length has to be a constant", spelled));
        }
        if (d.isArray || !isInteger(d.kind)) {
            self.err(format("`{}` is not an integer, so it cannot be a length", spelled));
        }
        if (depth == 0) {
            if (d.visibility == Vis.Local && d.file != self.lx.currentFile) {
                self.err(format("`{}` is private to `{}`\nhelp: declare it `pkg` or `pub` to use it from another file", spelled, nameOf(d.file)));
            }
            if (d.visibility == Vis.Pkg && d.pkg != self.lx.currentPackage) {
                self.err(format("`{}` is private to package `{}`\nhelp: declare it `pub` to use it from another package", spelled, nameOf(d.pkg)));
            }
        }
        if (d.init == NO_NODE) {
            self.err(format("`{}` has no initializer, so it has no value to use as a length", spelled));
        }
        q: str = nameOf(d.name);
        m: str = strSlice(q, 0, q.len - lastComponentOf(q).len);
        if (m.len >= 2) { m = strSlice(m, 0, m.len - 2); }
        return self.foldConst(d.init, m, depth + 1);
    }

    // `>` closes a type-argument list, but the lexer has already fused `>>` into one shift token,
    // which is exactly what `Vec<Vec<long>>` ends with. Splitting it here rather than in the lexer
    // keeps the shift operator a single token everywhere it really is one.
    atCloseAngle &self -> bool {
        return self.check(Tok.GreaterThan) || self.check(Tok.ShiftRight);
    }
    closeAngle &self -> void {
        if (self.eat(Tok.GreaterThan)) { return; }
        if (self.check(Tok.ShiftRight)) {
            self.cur = tokenOf(Tok.GreaterThan);              // one `>` consumed, one left
            return;
        }
        self.expect(Tok.GreaterThan);
    }

    // `Name<A, B>` in a type position. Produces the instance name (`Vec_long`) and asks for it
    // to be stamped out. Naming the instance here is what lets everything downstream treat a
    // generic use as an ordinary named type.
    //
    // An argument may be a length where the template takes one (`Buf<64>`, `Buf<PATH_MAX>`). A
    // length is mangled as its value, so two spellings of one value name one instance. Trailing
    // parameters may be left out: one with a default takes it, and inside the template's own
    // declaration and methods blocks a parameter left out means this instance's own (`Buf<T>`
    // there is `Buf<T, N>`, the type being written).
    parseGenericArgs &self base:Sym -> TypeRef {
        self.expect(Tok.LessThan);
        args: Vec<TypeRef>;
        while (!self.atCloseAngle() && !self.check(Tok.FileEnd)) {
            self.lenArgOk = true;
            args.push(self.parseTypeRef());
            self.lenArgOk = false;
            self.eat(Tok.Comma);
        }
        self.closeAngle();
        return self.instanceOf(base, args);
    }

    // `Buf` written bare, outside its own declaration and methods blocks, where every parameter
    // has a default: the instance at the defaults, as `Buf<>` would be. A template with a
    // parameter that must be given stays a template's name, which is what it always meant.
    defaultInstance &self q:Sym -> TypeRef {
        r: TplRef = self.tplRef(q);
        if (q == self.selfTpl || !r.known || r.count == 0) { return TypeRef { base: Lit.Struct, name: q }; }
        for k in 0..r.count {
            if (self.tplInfo(r, k).deflt.base == Lit.Void) { return TypeRef { base: Lit.Struct, name: q }; }
        }
        none: Vec<TypeRef>;
        return self.instanceOf(q, none);
    }

    // `base<args>` as a type: each argument held to its parameter's kind, the ones left out
    // filled in, and the instance named and asked for.
    instanceOf &self base:Sym sink args:Vec<TypeRef> -> TypeRef {
        r: TplRef = self.tplRef(base);
        if (r.known) {
            spelled: str = lastComponentOf(nameOf(base));
            if (args.len() > r.count) {
                self.err(format("wrong number of type arguments to `{}`: expected at most {}, found {}", spelled, r.count, args.len()));
            }
            k: long = 0;
            while (k < args.len()) {
                a: TypeRef = args.get(k);
                isLen: bool = a.base == Lit.Len || (a.base == Lit.TypeVar && self.isLenVar(a.name));
                want: bool = self.tplInfo(r, k).isLen;
                if (want && !isLen) {
                    self.err(format("expected a length for parameter `{}` of `{}`, found type `{}`\nhelp: give it a length: an integer or a constant",
                                    nameOf(self.tplName(r, k)), spelled, typeMangleName(a.base, a.name)));
                }
                if (!want && isLen) {
                    self.err(format("expected a type for parameter `{}` of `{}`, found length `{}`",
                                    nameOf(self.tplName(r, k)), spelled, typeMangleName(a.base, a.name)));
                }
                k = k + 1;
            }
            while (args.len() < r.count) {
                k = args.len();
                d: TypeRef = self.tplInfo(r, k).deflt;
                if (r.own) {
                    args.push(TypeRef { base: Lit.TypeVar, name: self.tplName(r, k) });
                } else if (d.base != Lit.Void) {
                    args.push(d);
                } else {
                    self.err(format("wrong number of type arguments to `{}`: expected {}, found {}\nnote: parameter `{}` has no default",
                                    spelled, r.count, k, nameOf(self.tplName(r, k))));
                }
            }
        }

        s: String;
        s.pushStr(nameOf(base));
        for i in 0..args.len() {
            a: TypeRef = args.get(i);
            s.push('_');
            s.pushStr(typeMangleName(a.base, a.name));
        }
        instance: Sym = NO_SYM;
        instance = internString(s);
        // A template not declared yet may be declared below; if the module ends without one, the
        // use is refused there (`checkImplTraits`).
        if (!r.known && self.quoteDepth == 0) {
            self.implChecks.push(ImplCheck { trait: base, owner: NO_SYM, line: self.lx.fileLine,
                                             col: self.lx.charNumber, file: self.lx.currentFile,
                                             isType: true });
        }
        regRequest(base, instance, args, self.plainBody);
        return TypeRef { base: Lit.Struct, name: instance };
    }

    // `struct Name<T> { ... }` and `enum Name<T> { ... }`: a pattern for making types, not a
    // type. The fields are recorded with their types unresolved, because a field's type may be one
    // of the parameters; substitution happens per instance.
    parseGenericStruct &self bare:Sym -> long {
        self.requireTypeNameFree(nameOf(bare));
        q: Sym = self.qualify(nameOf(bare));
        // Into a local, then handed over: lending `self.tplBounds` to a call that also lends
        // `self` is two lends of one value, which the exclusivity check refuses.
        bs: Vec<MethodBound>;
        params: Vec<Sym> = self.parseParamNamesInto(&bs);
        self.tplBounds = bs;
        self.beginOwnTemplate(q, params);
        self.expect(Tok.LeftCurly);

        fields: Vec<GField>;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            fname: Token = self.expect(Tok.Id);
            self.expect(Tok.Colon);
            if (self.check(Tok.LeftSquare)) {
                self.advance();
                elem: TypeRef = self.parseTypeRef();
                self.expect(Tok.Semicolon);
                n: long = self.parseArrayLength();
                self.expect(Tok.RightSquare);
                fields.push(GField { name: fname.text, kind: elem, isArray: true, count: n });
            } else {
                t: TypeRef = self.parseTypeRef();
                fields.push(GField { name: fname.text, kind: t, isArray: false, count: 0 });
            }
            self.eat(Tok.Comma);
        }
        self.expect(Tok.RightCurly);
        self.clearTypeVars();
        self.leaveTemplate();
        self.recordTemplate(q, params, fields, false);
        self.ast.structDecls.push(q);
        return self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1);
    }

    parseGenericEnum &self bare:Sym -> long {
        self.requireTypeNameFree(nameOf(bare));
        q: Sym = self.qualify(nameOf(bare));
        // Into a local, then handed over: lending `self.tplBounds` to a call that also lends
        // `self` is two lends of one value, which the exclusivity check refuses.
        bs: Vec<MethodBound>;
        params: Vec<Sym> = self.parseParamNamesInto(&bs);
        self.tplBounds = bs;
        self.beginOwnTemplate(q, params);
        self.expect(Tok.LeftCurly);

        fields: Vec<GField>;
        variants: Vec<GVariant>;
        next: long = 0;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) {
            vname: Token = self.expect(Tok.Id);
            n: long = 0;
            if (self.eat(Tok.LeftParen)) {
                while (!self.check(Tok.RightParen) && !self.check(Tok.FileEnd)) {
                    t: TypeRef = self.parseTypeRef();
                    fields.push(GField { name: enumPayloadField(nameOf(vname.text), n),
                                         kind: t, isArray: false, count: 0 });
                    n = n + 1;
                    self.eat(Tok.Comma);
                }
                self.expect(Tok.RightParen);
            }
            if (self.eat(Tok.Equals)) { next = self.expect(Tok.IntLiteral).num; }
            variants.push(GVariant { name: vname.text, value: next, payloadCount: n });
            next = next + 1;
            self.eat(Tok.Comma);
        }
        self.expect(Tok.RightCurly);
        self.clearTypeVars();
        self.leaveTemplate();
        self.recordTemplateWith(q, params, fields, variants, true);
        self.ast.structDecls.push(q);
        return self.ast.addStmt(StmtKind.StructDecl, self.ast.structDecls.len() - 1);
    }

    recordTemplate &self q:Sym params:Vec<Sym> fields:Vec<GField> isEnum:bool -> void {
        vs: Vec<GVariant>;
        self.recordTemplateWith(q, params, fields, vs, isEnum);
    }

    recordTemplateWith &self q:Sym params:Vec<Sym> fields:Vec<GField> vs:Vec<GVariant> isEnum:bool -> void {
        // What each parameter is, from the header just read (`tplParams`, read like `tplBounds`
        // and for the same reason); a template with no header of its own (a closure's capture
        // struct) is over the parameters in scope, as they are.
        infos: Vec<GParamInfo>;
        if (self.tplParams.len() == params.len()) { infos.extend(self.tplParams); }
        else { infos = self.paramInfosOf(params); }
        // The bounds the header collected, read from the scratch field rather than threaded
        // through: `recordTemplateWith` is called from two places and already takes five.
        bs: Vec<MethodBound>;
        bs.extend(self.tplBounds);
        regAddTemplate(q, params, infos, fields, vs, bs, isEnum, self.vis,
                       self.lx.currentFile, self.lx.currentPackage);
    }

    // `Fn(A, B) -> R` as the trait it stands for. The arity picks which of `Fn0`..`Fn4` it is,
    // and the return type is the last argument, so `Fn(&T) -> void` is `Fn1<&T, void>`. `Fn` is
    // read as a name like any other, so this is reached only after the `(` proves it is the sugar.
    parseFnSugar &self -> TypeRef {
        t: TraitRef = self.parseFnTrait();
        // Stamped like any other trait used as a type, so `Fn(long) -> long` has signatures to
        // dispatch through and a vtable to point at, not just a name.
        args: Vec<TypeRef>;
        for k in 0..t.argCount { args.push(gReg.traitArgAt(t, k)); }
        return TypeRef { base: Lit.TraitObj, name: regStampTrait(t.name, args) };
    }

    // `Fn(A, B) -> R` as the trait it stands for, arguments intact. A bound needs them (that is
    // how `F: Fn(&T) -> U` says what U is) so the mangling happens only where a type is wanted.
    parseFnTrait &self -> TraitRef {
        self.expect(Tok.LeftParen);
        args: Vec<TypeRef>;
        while (!self.check(Tok.RightParen) && !self.check(Tok.FileEnd)) {
            // A callable may say how it takes an argument (`Fn(sink U, &T)`) exactly as a fn
            // type may. It is part of the contract, not a type of its own: read as one, it would
            // become an extra argument, and the sugar would ask for `Fn3` where it meant `Fn2`.
            if (!self.eatWord("sink")) { self.eatWord("read"); }
            args.push(self.parseTypeRef());
            self.eat(Tok.Comma);
        }
        self.expect(Tok.RightParen);
        self.expect(Tok.Arrow);
        args.push(self.parseTypeRef());                 // the result, last as the trait declares it
        // No ceiling: the trait for this arity is made if it does not exist yet.
        base: Sym = self.fnTraitFor(args.len() - 1);
        return TraitRef { name: base, firstArg: gReg.addTraitArgs(args), argCount: args.len() };
    }

    // `Trait` or `Trait<A, B>` after `for`. Read as a trait rather than as a type: `Eq<str>` names
    // one implementation of a parameterized trait, not an instance of a generic struct, and
    // stamping it as the latter would ask for a type nobody declared.
    parseTraitRef &self -> TraitRef {
        if (self.word("Fn")) {
            self.advance();
            if (self.check(Tok.LeftParen)) { return self.parseFnTrait(); }
            self.err(stringOf("`Fn` needs a signature\nhelp: write `Fn(A) -> R`"));
        }
        name: Token = self.expect(Tok.Id);
        q: Sym = self.qualifiedFrom(name);
        args: Vec<TypeRef>;
        if (self.check(Tok.LessThan)) {
            self.advance();
            while (!self.atCloseAngle() && !self.check(Tok.FileEnd)) {
                args.push(self.parseTypeRef());
                self.eat(Tok.Comma);
            }
            self.closeAngle();
        }
        return TraitRef { name: q, firstArg: gReg.addTraitArgs(args), argCount: args.len() };
    }

    // The template parameters in scope. A flat list rather than a stack of frames: templates do
    // not nest here, and a generic method's owner parameters and its own are one scope anyway.
    isTypeVar &self name:Sym -> bool {
        for i in 0..self.typeVars.len() {
            if (self.typeVars.get(i) == name) { return true; }
        }
        return false;
    }
    clearTypeVars &self -> void { self.typeVars.clear(); self.lenVars.clear(); }

    // `name<T> args -> R { }`: a generic function. Its body is parsed with the parameters in
    // scope as type variables, and the whole definition is kept as a template.
    parseGenericFunction &self bare:Sym -> long {
        bs: Vec<MethodBound>;
        params: Vec<Sym> = self.parseParamNamesInto(&bs);
        // Kept across the body, which may read headers of its own (a closure records one).
        header: Vec<GParamInfo>;
        header.extend(self.tplParams);
        // Recorded before the definition, which copies the range onto its node: a call reads
        // them back to work out a parameter no argument mentions.
        self.boundFirst = regAddBounds(bs);
        self.boundCount = bs.len();
        st: long = self.parseFunctionDef(bare);
        self.tplParams = header;
        self.boundCount = 0;
        self.clearTypeVars();
        // The definition just parsed is a pattern: its parameter types are still type variables,
        // and a call is what says what they are. Everything after this skips it, and
        // monomorphization clones it per instantiation.
        at: long = self.ast.stmts.get(st).at;
        f: FnNode = self.ast.fns.get(at);
        // A generic has no symbol until its type is known: `first<T>` is a pattern, and what gets
        // emitted is `first_long`, stamped where the call is. So there is nothing for a linker to
        // find, and a declaration without a body cannot be one. Every language with monomorphized
        // generics has this boundary (Rust ships MIR in an rlib, C++ puts the template in the
        // header), and here it means the definition crosses as source.
        if (f.body < 0) {
            self.err(format("generic function `{}` has no body\nnote: a generic function has no symbol to link against, so a declaration without a body cannot take type parameters\nhelp: include the definition instead",
                            nameOf(bare)));
        }
        f.isTemplate = true;
        self.ast.fns.set(at, f);
        // Recorded as a template with no fields: what monomorphization needs from a function is
        // its parameter names and its body, and the body is already the statement above.
        empty: Vec<GField>;
        // Its own bounds, not whatever header was read last.
        fnode: FnNode = self.ast.fns.get(self.ast.stmts.get(st).at);
        held: Vec<MethodBound>;
        held.extend(self.tplBounds);
        self.tplBounds.clear();
        for k in 0..fnode.boundCount { self.tplBounds.push(gReg.boundAt(fnode.firstBound + k)); }
        self.recordTemplate(fnode.name, params, empty, false);
        self.tplBounds = held;
        return st;
    }
}

methods Parser {
    // ─── qualified names ─────────────────────────────────────────────────────

    // `mod::Name`, spelled out. A name is always reachable through the module that declared it,
    // which is what makes two modules able to use the same one.
    //
    // Returns the qualified symbol and leaves the cursor after the last component. The leading
    // identifier is already consumed.
    qualifiedFrom &self first:Token -> Sym {
        if (!self.check(Tok.ColonColon)) {
            return self.resolveHere(nameOf(first.text));
        }
        self.advance();
        second: Token = self.expect(Tok.Id);
        s: String;
        s.pushStr(nameOf(first.text));
        s.pushStr("::");
        s.pushStr(nameOf(second.text));
        out: Sym = NO_SYM;
        out = internString(s);
        return out;
    }
}

methods Parser {
    // `(a, b, ...)`: a structural aggregate. The first element is already parsed; the comma that
    // told them apart from a parenthesised expression is still the current token.
    parseTupleLit &self first:NodeId -> NodeId {
        inits: Vec<InitNode>;
        inits.push(InitNode { name: NO_SYM, value: first });
        while (self.eat(Tok.Comma)) {
            if (self.check(Tok.RightParen)) { break; }
            inits.push(InitNode { name: NO_SYM, value: self.parseExpr() });
        }
        self.expect(Tok.RightParen);
        at: long = self.ast.addInits(inits);
        self.ast.lits.push(LitNode { typeName: NO_SYM, firstInit: at, initCount: inits.len(),
                                     rest: NO_NODE });
        return self.ast.leaf(Op.TupleLit, Payload.Lit(self.ast.lits.len() - 1), Lit.Tuple);
    }
}

methods Parser {
    // `q, r, ... = tupleCall();`: the names are fresh locals; what each one's type really is
    // comes from the tuple's fields, which the middle end fills in.
    //
    // A destructure either declares every name or assigns to places that all exist: a name that
    // is a local (or a parameter) here is assigned, one that is not is declared, and one of each
    // is refused rather than guessed at.
    parseDestructure &self first:Sym -> long {
        spelled: Vec<Sym>;
        spelled.push(first);
        while (self.eat(Tok.Comma)) {
            n: Token = self.expect(Tok.Id);
            if (nameOf(n.text) != "_" && self.bindingOf(n.text).renamed != NO_SYM) { self.refuseMixedDestructure(n.text, first); }
            spelled.push(n.text);
        }
        self.expect(Tok.Equals);
        // Read before the names are declared, so `a, b = f(a)` with an outer `a` reads that one.
        value: NodeId = self.parseExpr();
        self.expect(Tok.Semicolon);
        // `_` declares nothing: the checker releases that element at once (`desugarDestructure`).
        names: Vec<Sym>;
        for n in spelled {
            if (nameOf(n) == "_") { names.push(n); } else { names.push(self.declareLocal(n, Lit.Long, NO_SYM)); }
        }
        return self.destructureStmt(names, value);
    }

    // `_ = value;`: evaluated, and what it yields released at once. A hidden local of the value's
    // own type (settled by the checker at the store) in a block of its own, so it is released at
    // the statement's end: `{ $discN: <infer>; $discN = value; }`. A `MustUse` value is used by
    // the binding, which is what makes this the way to say a result is dropped on purpose.
    parseDiscard &self -> long {
        self.expect(Tok.Equals);
        value: NodeId = self.parseExpr();
        self.expect(Tok.Semicolon);
        self.pushScope();
        seq: long = self.uniq;
        self.uniq = self.uniq + 1;
        ids: Vec<long>;
        self.inferPair(internString(format("$disc{}", seq)), value, &ids);
        self.popScope();
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(ids) });
        return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
    }

    destructureStmt &self names:Vec<Sym> value:NodeId -> long {
        at: long = self.ast.addNames(names);
        self.ast.destructures.push(DestructureNode { firstName: at, nameCount: names.len(),
                                                     value: value });
        return self.ast.addStmt(StmtKind.Destructure, self.ast.destructures.len() - 1);
    }

    // `leaf, pos = db.advance(leaf, pos);` and `self.a, n = ...`: every target a place that already
    // exists. Written as a block that takes the tuple apart into hidden locals and assigns each one
    // to its target, so every target is stored into the way `x = v` stores (the old value
    // released, the new one moved in) and the value is read whole before any target is written:
    //
    //     { $dstN_0, $dstN_1 = value; leaf = $dstN_0; pos = $dstN_1; }
    parseDestructureInto &self first:NodeId firstName:Sym -> long {
        why: String = stringOf("a destructure assigns to places: a local, a field, an element or `*p`");
        targets: Vec<NodeId>;
        targets.push(first);            // NO_NODE: `_`, an element released at the block's end
        while (self.eat(Tok.Comma)) {
            if (self.check(Tok.Id) && nameOf(self.cur.text) == "_" && self.bindingOf(self.cur.text).renamed == NO_SYM
                && (self.peekNext().kind == Tok.Comma || self.peekNext().kind == Tok.Equals)) {
                self.advance();
                targets.push(NO_NODE);
                continue;
            }
            if (self.check(Tok.Id) && self.bindingOf(self.cur.text).renamed == NO_SYM
                && (self.peekNext().kind == Tok.Comma || self.peekNext().kind == Tok.Equals)) {
                self.refuseMixedDestructure(firstName, self.cur.text);
            }
            tAt: long = self.curPos;
            t: NodeId = self.parseExpr();
            self.refuseNonPlace(t, tAt, why);
            targets.push(t);
        }
        self.expect(Tok.Equals);
        value: NodeId = self.parseExpr();
        self.expect(Tok.Semicolon);

        self.pushScope();
        seq: long = self.uniq;
        self.uniq = self.uniq + 1;
        names: Vec<Sym>;
        for j in 0..targets.len() {
            names.push(self.declareLocal(internString(format("$dst{}_{}", seq, j)), Lit.Long, NO_SYM));
        }
        ids: Vec<long>;
        ids.push(self.destructureStmt(names, value));
        for j in 0..targets.len() {
            lhs: NodeId = targets.get(j);
            if (lhs == NO_NODE) { continue; }
            rhs: NodeId = self.nameRef(names.get(j), Lit.Long, NO_SYM);
            e: NodeId = self.ast.binary(Op.Assignment, lhs, rhs, self.ast.expr(lhs).kind);
            self.ast.exprStmts.push(ExprStmtNode { value: e });
            ids.push(self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1));
        }
        self.popScope();
        self.ast.blockStmts.push(BlockStmtNode { body: self.ast.addBlock(ids) });
        return self.ast.addStmt(StmtKind.Block, self.ast.blockStmts.len() - 1);
    }

    // Something a store can go to.
    isPlace &self e:NodeId -> bool { return isPlaceOp(self.ast.expr(e).op); }

    // A store to something that is not a place goes to a value made for the statement and thrown
    // away with it, so it can never mean what it says: `(a, b) = (b, a)` builds a new tuple and
    // swaps nothing, `f() = 3` writes the call's result, `S { x: 1 } = s` a fresh struct. Each is
    // refused at the target, `at`, with `why` (what the statement needs) as the note. A place in
    // parentheses, `(x) = 1`, is still that place. In a quote, `@x` is code still to be made, and
    // is taken as written.
    refuseNonPlace &self lhs:NodeId at:long why:String -> void {
        if (self.isPlace(lhs)) { return; }
        e: Expr = self.ast.expr(lhs);
        if (e.op == Op.Splice && self.quoteDepth > 0) { return; }
        msg: String = format("cannot assign to {}", nonPlaceText(self.ast, lhs));
        if (e.op == Op.TupleLit) {
            // The destructure the parentheses stand in the way of, spelled with the user's own
            // names when every element is one.
            names: String;
            plain: bool = true;
            match e.payload {
                Lit(ix) {
                    ln: LitNode = self.ast.lits.get(ix);
                    for k in 0..ln.initCount {
                        el: Expr = self.ast.expr(self.ast.inits.get(ln.firstInit + k).value);
                        match el.payload {
                            Name(n) { if (el.op == Op.Lvalue) { if (k > 0) { names.pushStr(", "); } names.pushStr(sourceName(n)); } else { plain = false; } }
                            _ { plain = false; }
                        }
                    }
                }
                _ { plain = false; }
            }
            if (!plain || names.length() == 0) { names = stringOf("a, b"); }
            help: String = format("\nnote: the parentheses make a new tuple, and a store into it would be lost\nhelp: to assign each element, write `{} = ...` without the parentheses", names);
            msg.pushString(help);
        } else {
            msg.pushStr("\nnote: ");
            unsafe { msg.pushStr(why.view()); }
        }
        if (at == 0 || posFile(at) == NO_SYM) { self.err(msg); return; }
        self.errAt(at, msg);
    }

    // `local` is a local here and `fresh` is not (`local` is NO_SYM when the other targets are
    // places rather than bare names).
    refuseMixedDestructure &self local:Sym fresh:Sym -> void {
        if (local != NO_SYM) {
            self.err(format("cannot mix new names and existing locals in a destructure\nnote: `{}` is a local here and `{}` is not\nhelp: declare `{}` first, or give `{}` a new name",
                            nameOf(local), nameOf(fresh), nameOf(fresh), nameOf(local)));
            return;
        }
        self.err(format("cannot mix new names and places in a destructure\nnote: `{}` is not a local here\nhelp: declare `{}` first",
                        nameOf(fresh), nameOf(fresh)));
    }
}

methods Parser {
    // `quote { expr }`. Entry: `quote` has been consumed.
    parseQuote &self -> NodeId {
        self.expect(Tok.LeftCurly);
        node: Sym = self.resolveHere("Node");
        if (gReg.findEnumSym(node) < 0 || gReg.findEnumSym(self.resolveHere("BinOp")) < 0
            || gReg.findEnumSym(self.resolveHere("UnOp")) < 0) {
            self.err(stringOf("`quote` needs `stdlib::ast`\nhelp: add `#include <stdlib::ast>`"));
        }
        q: Quoter = self.quoter();
        self.quoteDepth = self.quoteDepth + 1;
        self.pushScope();
        // `quote { methods T for Trait { ... } }`: a declaration, which a derive macro returns.
        if (self.word("methods") && !self.namedHere()) {
            self.advance();
            decl: NodeId = self.parseQuotedMethods(q);
            self.expect(Tok.RightCurly);
            self.popScope();
            self.quoteDepth = self.quoteDepth - 1;
            return decl;
        }
        ids: Vec<long>;
        // An expression, unless the first token can only open a statement. An expression that
        // turns out to be followed by `;` was the first of several statements.
        if (!self.opensStatement()) {
            first: NodeId = self.parseExpr();
            if (self.check(Tok.RightCurly)) {
                self.advance();
                self.popScope();
                self.quoteDepth = self.quoteDepth - 1;
                return q.quoteTree(&self.ast, first);
            }
            // `acc = acc + 1;` reads as an expression up to its `=`: an assignment statement.
            ids.push(self.finishAssignOrExpr(first));
        }
        rest: Vec<long> = self.parseStmtsUntilClose();
        ids.extend(rest);
        self.popScope();
        self.quoteDepth = self.quoteDepth - 1;
        if (ids.len() == 1) { return q.quoteStmt(&self.ast, ids.get(0)); }
        return q.quoteStmts(&self.ast, ids);
    }
    // Whether the token here can only begin a statement: a keyword, a block, a declaration.
    opensStatement &self -> bool {
        if (self.check(Tok.LeftCurly)) { return true; }
        if (self.check(Tok.Id) && self.peekNext().kind == Tok.Colon) { return true; }
        return (self.word("if") || self.word("while") || self.word("return") || self.word("break")
                || self.word("continue") || self.word("loop") || self.word("for") || self.word("match")
                || self.word("unsafe") || self.word("recover")) && !self.namedHere();
    }
    // The tokens up to the `]` that closes the one just read, spelled back out as source text with
    // one space between them. The lexer keeps no raw text, but the spelling of every kind is
    // known. Held as a string literal, so `\` and `"` are escaped for the literal to resolve back.
    rawUntilClose &self -> Sym {
        out: String;
        depth: long = 1;
        while (!self.check(Tok.FileEnd)) {
            if (self.check(Tok.LeftSquare)) { depth = depth + 1; }
            if (self.check(Tok.RightSquare)) {
                depth = depth - 1;
                if (depth == 0) { self.advance(); return internString(out); }
            }
            t: Token = self.advance();
            if (out.len > 0) { out.push(' '); }
            self.respell(t, &out);
        }
        self.err(stringOf("unclosed `![`\nnote: the file ends before its `]`"));
        return NO_SYM;
    }
    respell &self t:Token inout out:String -> void {
        if (t.kind == Tok.Id || t.kind == Tok.Literal || t.kind == Tok.StringLiteral) {
            s: str = nameOf(t.text);
            for i in 0..s.len {
                c: long = charAt(s, i);
                if (c == 92 || c == 34) { out.push(92 as char); }     // a backslash or a quote, escaped for the literal
                out.push(c as char);
            }
            return;
        }
        if (t.kind == Tok.IntLiteral || t.kind == Tok.LongLiteral) { out.pushLong(t.num); return; }
        if (t.kind == Tok.U64Literal) { out.pushString(format("{}", t.num as u64)); return; }
        if (t.kind == Tok.FloatLiteral) { out.pushStr(nameOf(t.text)); return; }
        if (t.kind == Tok.CharLiteral) {
            // Back to a character literal, escaping what a literal escapes, and each backslash
            // once more, since this text is itself the body of a string literal.
            out.push(39 as char);
            c: long = t.num;
            if (c == 10)      { out.pushStr("\\\\n"); }
            else if (c == 9)  { out.pushStr("\\\\t"); }
            else if (c == 13) { out.pushStr("\\\\r"); }
            else if (c == 0)  { out.pushStr("\\\\0"); }
            else if (c == 92) { out.pushStr("\\\\\\\\"); }
            else if (c == 39) { out.pushStr("\\\\"); out.push(39 as char); }
            else { out.push(c as char); }
            out.push(39 as char);
            return;
        }
        out.pushStr(spellOf(t.kind));
    }
    // The three names a quote builds against, resolved where the quote is written.
    quoter &self -> Quoter {
        return Quoter { node: self.resolveHere("Node"), binOp: self.resolveHere("BinOp"), unOp: self.resolveHere("UnOp") };
    }

    // What a splice holds, read OUTSIDE the quote: `@x` the variable alone, `@(e)` the
    // expression in the parentheses. Entry: the `@` has been consumed.
    parseSpliceHeld &self -> NodeId {
        self.quoteDepth = self.quoteDepth - 1;
        held: NodeId = NO_NODE;
        if (self.eat(Tok.LeftParen)) {
            held = self.parseExpr();
            self.expect(Tok.RightParen);
        } else {
            t: Token = self.expect(Tok.Id);
            b: Binding = self.bindingOf(t.text);
            if (b.renamed != NO_SYM) { held = self.nameRef(b.renamed, b.kind, b.structName); }
            else { held = self.nameRef(t.text, Lit.Long, NO_SYM); }
        }
        self.quoteDepth = self.quoteDepth + 1;
        return held;
    }

    // `quote { methods T for Trait { ... } }`, as the `MethodsDecl` Node that builds it. Nothing
    // is declared: read the ordinary way, the block would register its functions and its impl
    // here, in the macro's own module, when it is only data until a derive splices it. Every
    // name in it (the type, the trait, a method, a parameter's type) may be `@(e)`, a `str` the
    // macro computes. Entry: `methods` has been consumed.
    parseQuotedMethods &self q:Quoter -> NodeId {
        owner: NodeId = self.parseQuotedType(q);
        trait: NodeId = q.qStr(&self.ast, intern(""));
        if (self.eatWord("for")) {
            if (self.eat(Tok.AtSign)) { trait = self.parseSpliceHeld(); }
            else { trait = q.qStr(&self.ast, self.expect(Tok.Id).text); }   // trait names are flat
        }
        self.expect(Tok.LeftCurly);
        fns: Vec<NodeId>;
        while (!self.check(Tok.RightCurly) && !self.check(Tok.FileEnd)) { fns.push(self.parseQuotedFn(q)); }
        self.expect(Tok.RightCurly);
        args: Vec<NodeId>;
        args.push(owner);
        args.push(trait);
        args.push(q.qList(&self.ast, fns));
        return q.qVariant(&self.ast, "MethodsDecl", args);
    }
    // One method of a quoted methods block, as an `FnDecl`: `name &self p:T -> R { body }`. The
    // parameters are declared for the body, so a mention of one names exactly it.
    parseQuotedFn &self q:Quoter -> NodeId {
        name: NodeId = NO_NODE;
        if (self.eat(Tok.AtSign)) { name = self.parseSpliceHeld(); }
        else { name = q.qStr(&self.ast, self.expect(Tok.Id).text); }
        self.pushScope();
        params: Vec<NodeId>;
        lent: bool = self.eat(Tok.Ampersand);
        if (lent || self.word("self")) {
            if (!self.eatWord("self")) { self.err(format("expected `self`, found {}", describeTok(self.cur))); }
            spelled: str = "Self";
            if (lent) { spelled = "ref_Self"; }
            self.declareLocal(intern("self"), Lit.Struct, NO_SYM);
            params.push(self.quotedParam(q, q.qStr(&self.ast, intern("self")), q.qStr(&self.ast, intern(spelled)), ""));
        }
        while (self.check(Tok.Id)) {
            conv: str = "";
            if (self.eatWord("inout"))     { conv = "inout"; }
            else if (self.eatWord("read")) { conv = "read"; }
            else if (self.eatWord("sink")) { conv = "sink"; }
            pname: Token = self.expect(Tok.Id);
            self.expect(Tok.Colon);
            ty: NodeId = self.parseQuotedType(q);
            renamed: Sym = self.declareLocal(pname.text, Lit.Struct, NO_SYM);
            params.push(self.quotedParam(q, q.qStr(&self.ast, renamed), ty, conv));
        }
        self.expect(Tok.Arrow);
        ret: NodeId = self.parseQuotedType(q);
        self.expect(Tok.LeftCurly);
        ids: Vec<long> = self.parseStmtsUntilClose();
        self.popScope();
        args: Vec<NodeId>;
        args.push(name);
        args.push(q.qList(&self.ast, params));
        args.push(ret);
        args.push(q.qBoxed(&self.ast, q.quoteStmts(&self.ast, ids)));
        return q.qVariant(&self.ast, "FnDecl", args);
    }
    quotedParam &self q:Quoter name:NodeId ty:NodeId conv:str -> NodeId {
        args: Vec<NodeId>;
        args.push(name);
        args.push(ty);
        args.push(q.qStr(&self.ast, intern(conv)));
        return q.qVariant(&self.ast, "ParamDecl", args);
    }
    // A type in a quoted declaration, as the `str` spelling the compiler mangles it to. `Self`
    // and `&Self` name the type the methods are for, which only the derive knows.
    parseQuotedType &self q:Quoter -> NodeId {
        if (self.check(Tok.Ampersand) && self.peekNext().kind == Tok.Id && nameOf(self.peekNext().text) == "Self") {
            self.advance();
            self.advance();
            return q.qStr(&self.ast, intern("ref_Self"));
        }
        if (self.word("Self")) { self.advance(); return q.qStr(&self.ast, intern("Self")); }
        t: TypeRef = self.parseTypeRef();
        return q.qType(&self.ast, t.base, t.name);
    }

    // ─── assert ──────────────────────────────────────────────────────────────

    // The tree back as source text, for a diagnostic that quotes what the writer wrote. Not a
    // pretty-printer: parentheses go around every binary operation, which is always correct and
    // never ambiguous, and anything without an obvious spelling prints as `<expr>`.
    unparse &self id:NodeId -> String {
        out: String;
        if (id == NO_NODE) { out.pushStr("<expr>"); return out; }
        e: Expr = self.ast.expr(id);
        if (e.left != NO_NODE) {
            out.push('(');
            out.pushString(self.unparse(e.left));
            out.push(' ');
            out.pushStr(opName(e.op));
            out.push(' ');
            out.pushString(self.unparse(e.right));
            out.push(')');
            return out;
        }
        if (e.op == Op.Literal) {
            match e.payload {
                Num(v) {
                    if (e.kind == Lit.Bool) { if (v != 0) { out.pushStr("true"); } else { out.pushStr("false"); } }
                    else { out.pushLong(v); }
                }
                _ { out.pushStr("<expr>"); }
            }
            return out;
        }
        if (e.op == Op.StringLit) {
            match e.payload { Text(t) { out.push('"'); out.pushStr(nameOf(t)); out.push('"'); } _ { } }
            return out;
        }
        if (e.op == Op.Lvalue) {
            match e.payload { Name(n) { out.pushStr(nameOf(n)); } _ { } }
            return out;
        }
        if (e.op == Op.LogicalNot || e.op == Op.BitwiseNot || e.op == Op.Deref) {
            if (e.op == Op.LogicalNot) { out.push('!'); }
            if (e.op == Op.BitwiseNot) { out.push('~'); }
            if (e.op == Op.Deref)      { out.push('*'); }
            match e.payload { Sub(v) { out.pushString(self.unparse(v)); } _ { } }
            return out;
        }
        if (e.op == Op.AddressOf) {
            out.push('&');
            match e.payload {
                Sub(v) {
                    inner: Expr = self.ast.expr(v);
                    if (inner.op == Op.Lvalue) { out.pushString(self.unparse(v)); } else { out.pushStr("<expr>"); }
                }
                _ { out.pushStr("<expr>"); }
            }
            return out;
        }
        if (e.op == Op.FieldAccess) {
            match e.payload {
                Field(i) {
                    f: FieldNode = self.ast.fields.get(i);
                    out.pushString(self.unparse(f.base));
                    out.push('.');
                    out.pushStr(nameOf(f.name));
                }
                _ { }
            }
            return out;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = self.ast.calls.get(0);
            match e.payload { Call(i) { c = self.ast.calls.get(i); } _ { } }
            if (e.op == Op.MethodCall) { out.pushString(self.unparse(c.receiver)); out.push('.'); }
            out.pushStr(nameOf(c.name));
            out.push('(');
            for k in 0..c.argCount {
                if (k > 0) { out.pushStr(", "); }
                out.pushString(self.unparse(self.ast.argAt(c, k)));
            }
            out.push(')');
            return out;
        }
        if (e.op == Op.ArrayIndex) {
            match e.payload {
                Index(i) {
                    ix: IndexNode = self.ast.indexes.get(i);
                    if (ix.base != NO_NODE) { out.pushString(self.unparse(ix.base)); } else { out.pushStr(nameOf(ix.name)); }
                    out.push('[');
                    if (ix.index != NO_NODE) { out.pushString(self.unparse(ix.index)); } else { out.pushStr(".."); }
                    out.push(']');
                }
                _ { }
            }
            return out;
        }
        out.pushStr("<expr>");
        return out;
    }

    // `assert!(cond);` -> `if (!(cond)) { panic("assertion failed: <cond as written>"); }`
    //
    // The built-in `assert!`, used unless the program declares a macro of that name. The
    // condition is captured unevaluated (it is `a == b`, not a bool), turned back into text for
    // the message, and spliced into ordinary code that the checker and the ownership pass then
    // read exactly as if a person had written the `if`. Entry: `assert` has been consumed.
    parseAssert &self -> long {
        self.expect(Tok.Exclamation);
        self.expect(Tok.LeftParen);
        cond: NodeId = self.parseExpr();
        self.expect(Tok.RightParen);
        self.eat(Tok.Semicolon);
        shown: String = self.unparse(cond);
        // Strip the outermost parentheses the unparser always adds: `assert!(a == b)` reads back
        // as `a == b`, not `(a == b)`.
        msg: String;
        msg.pushStr("assertion failed: ");
        s: str = "";
        unsafe { s = shown.view(); }
        if (s.len > 2 && charAt(s, 0) == '(' && charAt(s, s.len - 1) == ')') { msg.pushStr(strSlice(s, 1, s.len - 2)); }
        else { msg.pushStr(s); }
        args: Vec<NodeId>;
        args.push(self.ast.leaf(Op.StringLit, Payload.Text(internString(msg)), Lit.Str));
        q: Quoter = self.quoter();
        // The failure goes to the program's `@panic` function, which the checker finds by that
        // attribute (`Checker.panicTarget`): `$panic` is a name no source can spell, so no
        // function is reached by being called `panic`; a program that marks none cannot use the
        // built-in `assert!`.
        call: NodeId = q.qCall(&self.ast, "$panic", args);
        e: Expr = self.ast.expr(call);
        e.kind = Lit.Void;
        e.isParen = false;
        self.ast.setExpr(call, e);
        self.ast.exprStmts.push(ExprStmtNode { value: call });
        ids: Vec<long>;
        ids.push(self.ast.addStmt(StmtKind.Expr, self.ast.exprStmts.len() - 1));
        body: long = self.ast.addBlock(ids);
        notCond: NodeId = self.ast.unary(Op.LogicalNot, cond, Lit.Bool);
        self.ast.ifs.push(IfNode { cond: notCond, body: body, elseIf: -1 });
        return self.ast.addStmt(StmtKind.If, self.ast.ifs.len() - 1);
    }
}

// Which atomic primitive a `builtin` declaration's name selects (`BI_ATOMIC_*`), or 0: the six
// operations on an eight-byte word, and each again with `32` on a four-byte one.
local atomicBuiltinOf n:str -> long {
    base: str = n;
    wide: long = 0;
    if (n.len > 2 && strEndsWith(n, "32")) { base = strSlice(n, 0, n.len - 2); wide = BI_ATOMIC_32; }
    k: long = 0;
    if (base == "atomicLoad") { k = BI_ATOMIC_LOAD; }
    else if (base == "atomicStore") { k = BI_ATOMIC_STORE; }
    else if (base == "atomicStoreSeqCst") { k = BI_ATOMIC_STORE_SC; }
    else if (base == "atomicSwap") { k = BI_ATOMIC_SWAP; }
    else if (base == "atomicCas") { k = BI_ATOMIC_CAS; }
    else if (base == "atomicAdd") { k = BI_ATOMIC_ADD; }
    if (k == 0) { return 0; }
    return k + wide;
}
