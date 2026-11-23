// The `.klib`: one package, compiled once.
//
// An `ar` archive, the way a Rust `.rlib` is: the package's object file, which `ld` links
// straight out of the archive, and a member named `kiln.meta` that `ld` never looks at, because
// no symbol is defined in it. The metadata says what the package is and everything a dependent
// needs in place of compiling it again. A text header, then a binary body:
//
//     kiln-klib 9                         the format, refused unless exact
//     package <name>   key <hex>          what was built, and from what (the content key)
//     dep <name> <key>                    each direct dependency, and the key it was built against
//     extra <path>                        a module read from below the package's root directory
//     init <symbol>  entry <0|1>          its startup initializer, if any; whether it has `main`
//     body <bytes> <hash>                 the body's length and MurmurHash3-128, then the body
//
// The body is chunks, each a tag and a length (LEB128) and its bytes, so a reader skips a tag it
// does not know. A name anywhere in it is a position in the STRINGS chunk (`Sym`'s codec):
//
//     STRINGS     every name the body mentions, once: a count, each length, the bytes
//     EXPORTS     what the object defines for others
//     STAMPED     every generic struct instance it stamped
//     INSTANCES, VTABLES   the local symbols the object holds
//     INSTFNS     the generic instance functions it compiled and exports, each with the alias it
//                 is linked by, what it was compiled against, and its facts
//     IR          the optimized IR of what it exports that an inliner would copy, by link label
//                 (`codegen::irpack`), for a dependent to inline
//     EFFECTS     what each function it exports may write, by link label (`codegen::effects`),
//                 for a dependent's `flow.k` to keep what a call to one cannot reach
//     POISON      the globals a startup initializer may write
//     IMAGES      the folded globals' images: bytes, and where the pointers in them are
//     MODDIR      per module, in the order its compile scanned them: its path, package and
//                 includes, whether it declares a macro, and where its section is in MODULES
//     MODULES     the module sections (`KlibTree`): each module's tree as its parser produced it
//                 (registry operations, declarations, facts, bodies), so a dependent neither
//                 scans, preprocesses, lexes nor parses any of this package's files
//
// The body is hashed once as a whole, and checked when it is read, so the readers after that
// trust it. Every free-form string in the header is `<length>:<bytes>`.
#include <support::compiler>
#include <transform::facts>
#include <parse::upstream>
#include <pre::Preprocessor>
#include <codegen::{asm, irpack, effects}>
#include <stdlib::{encode, file, textfile, chars, map, option, result, string, vec, hash128, sort}>

pub KLIB_FORMAT: str = "kiln-klib 9";
pub KLIB_META: str = "kiln.meta";

// The chunk tags. A reader skips a tag it does not know, so a later format can add one.
pub CHUNK_STRINGS: long = 1;
pub CHUNK_EXPORTS: long = 2;
pub CHUNK_STAMPED: long = 3;
pub CHUNK_INSTANCES: long = 4;
pub CHUNK_VTABLES: long = 5;
pub CHUNK_POISON: long = 6;
pub CHUNK_IMAGES: long = 7;
pub CHUNK_MODDIR: long = 8;
pub CHUNK_MODULES: long = 9;
pub CHUNK_NAMEINDEX: long = 10;      // reserved: a name-to-declaration index (part 3)
pub CHUNK_INSTFNS: long = 11;
pub CHUNK_IR: long = 12;
pub CHUNK_EFFECTS: long = 13;
// A module section's (`KlibTree`).
pub CHUNK_OPS: long = 20;
pub CHUNK_DECLS: long = 21;
pub CHUNK_FACTS: long = 22;
pub CHUNK_BODYIX: long = 23;
pub CHUNK_BODIES: long = 24;

pub putChunk inout out:Encoder tag:long body:[u8] -> void {
    out.putUvarint(tag as u64);
    out.putBytes(body);
}

// One module of a package, in MODDIR: where its section is, in MODULES.
pub struct ModRec { path: str, pkg: str, includes: Vec<str>, hasMacro: bool, at: long, len: long }

// One module a loaded `.klib` carries: its package, its includes (a run in `gKlibIncludes`),
// whether it declares a macro (the scanner pulls `stdlib::ast` in for one), and its section.
pub struct KlibModule { path: str, pkg: str, firstInclude: long, includeCount: long, hasMacro: bool,
                        klib: long, at: long, len: long }

// One loaded `.klib`'s header, and where its body's parts are: the body (a view of the metadata,
// which is kept), its names (`gSymIn` from `symBase`, `symCount` of them), its images in
// `gFacts` (from `imageBase`), and its MODULES chunk.
pub struct KlibInfo { name: str, key: str, path: str, init: str, entry: bool,
                      firstDep: long, depCount: long,
                      body: str, symBase: long, symCount: long, imageBase: long, modulesAt: long }
pub struct KlibDep { name: str, key: str }

pub var gKlibs: Vec<KlibInfo> = vec![];
pub var gKlibDeps: Vec<KlibDep> = vec![];
pub var gKlibModules: Vec<KlibModule> = vec![];
pub var gKlibModuleAt: HashMap<str, long> = map![];
pub var gKlibIncludes: Vec<str> = vec![];

// ─── reading the archive ─────────────────────────────────────────────────────

// The metadata member of the archive at `path`, or the whole file when it is a bare `.meta`
// (what a build hands a dependent before the object has been archived). Only the member headers
// are read on the way to it: the object beside it may be megabytes.
pub readKlibMeta path:str -> Result<String, long> { return readKlibMetaUpTo(path, -1); }

// The same, at most `limit` bytes of it (all of it for -1): what a header is read from.
pub readKlibMetaUpTo path:str limit:long -> Result<String, long> {
    if (strEndsWith(path, ".meta")) {
        whole: Result<String, long> = readFileString(path);
        return whole;
    }
    f: Result<File, long> = File.openRead(path);
    match f {
        Err(e) { return Result.Err(e); }
        Ok(file) {
            out: Result<String, long> = metaMember(&file, limit);
            file.close();
            return out;
        }
    }
    return Result.Err(5);
}

// Walk the members: an 8-byte magic, then per member a 60-byte header (name in the first 16
// bytes, decimal size at 48) and the data, padded to an even length.
local metaMember inout f:File limit:long -> Result<String, long> {
    head: [u8; 60];
    n: long = 0;
    unsafe { n = f.readInto(&head, 8); }
    if (n != 8 || !(asText(head[0..8]) == "!<arch>\n")) { return Result.Err(8); }   // ENOEXEC
    at: long = 8;
    loop {
        f.seek(at, Seek.Set);
        unsafe { n = f.readInto(&head, 60); }
        if (n != 60) { return Result.Err(2); }                 // no metadata member
        size: long = 0;
        k: long = 48;
        while (k < 58 && head[k] >= '0' && head[k] <= '9') { size = size * 10 + (head[k] as long) - '0'; k = k + 1; }
        name: str = asText(head[0..16]);
        if (strStartsWith(name, "kiln.meta/")) {
            out: String;
            if (limit >= 0 && size > limit) { size = limit; }
            out.reserve(size);
            got: long = 0;
            unsafe { got = f.readInto(out.buf as long, size); }
            if (got != size) { return Result.Err(5); }
            out.len = size;
            return Result.Ok(out);
        }
        at = at + 60 + size + (size & 1);
    }
    return Result.Err(2);
}

local asText b:[u8] -> str { return b as str; }

// ─── whether a `.klib` can be used ───────────────────────────────────────────

// Whether a `.klib` can be used as it is, and if not, why, as a phrase that reads after "its
// cached .klib" or "it": "is damaged (...)", "was written in another format (...)". A value, not
// an error: a build rebuilds the package from its source and says why (`Build.k`). Only a compile
// handed one it cannot use stops, since it has no source to rebuild from (`cannotUse`).
pub struct KlibCheck { ok: bool, why: String }

pub klibUsable -> KlibCheck { return KlibCheck { ok: true, why: stringOf("") }; }
pub klibDamaged what:String -> KlibCheck { return KlibCheck { ok: false, why: format("is damaged ({})", what) }; }

// What a failed read of the archive says (`metaMember`'s answers).
local klibUnreadable e:long -> KlibCheck {
    if (e == 8) { return klibDamaged(stringOf("it is not an archive")); }
    if (e == 2) { return klibDamaged(stringOf("it has no `kiln.meta` member")); }
    if (e == 5) { return klibDamaged(stringOf("it is cut short inside its metadata")); }
    return KlibCheck { ok: false, why: format("cannot be read (errno {})", e) };
}

// The metadata's first line: this compiler's format, another's, or nothing a compiler wrote.
local formatCheck first:str -> KlibCheck {
    if (first == KLIB_FORMAT) { return klibUsable(); }
    if (strStartsWith(first, "kiln-klib ") && first.len < 32) {
        return KlibCheck { ok: false, why: format("was written in another format (`{}`; this compiler reads `{}`)", first, KLIB_FORMAT) };
    }
    return klibDamaged(stringOf("its metadata does not start with a `kiln-klib` line"));
}

// A `.klib` that this compile was handed and cannot use. A build would rebuild the package from
// its source; a compile has none, so it stops, naming the file and why.
pub cannotUse name:str path:str c:KlibCheck -> never {
    failStr(format("cannot use `{}` for package `{}`: it {}\nhelp: rebuild it with `kilnc build`", path, name, c.why));
}

// The header of a `.klib`'s metadata: what the package is, what it was built against, and its
// body, which the header's hash has been checked against.
pub struct KlibHead { name: str, key: str, init: str, entry: bool, deps: Vec<KlibDep>, body: str }

pub klibHeadOf -> KlibHead {
    return KlibHead { name: "", key: "", init: "", entry: false, deps: vec![], body: "" };
}

// The metadata `text` read into `h` and checked: its format, every header line up to the body,
// and the body's length and hash. The views in `h` are of `text`.
pub readKlibHead text:str inout h:KlibHead -> KlibCheck {
    m: MetaIn = metaIn(text);
    f: KlibCheck = formatCheck(m.restOfLine());
    if (!f.ok) { return f; }
    going: bool = true;
    while (going) {
        if (m.atEnd()) { m.bad(stringOf("`body`")); going = false; continue; }
        w: str = m.word();
        if (w == "package") { h.name = keep(m.text0()); }
        else if (w == "key") { h.key = keep(m.word()); }
        else if (w == "dep") {
            dn: str = keep(m.text0());
            dk: str = keep(m.word());
            h.deps.push(KlibDep { name: dn, key: dk });
        }
        else if (w == "extra") { m.text0(); }
        else if (w == "init") {
            s: Sym = m.name();
            if (s != NO_SYM) { h.init = nameOf(s); }
        }
        else if (w == "entry") { h.entry = m.num() != 0; }
        else if (w == "body") {
            n: long = m.num();
            want: str = m.word();
            h.body = m.blob(n);
            if (m.ok()) {
                hh: Hash128 = hash128Str(h.body);
                got: String = hh.hex();
                same: bool = false;
                unsafe { same = got.view() == want; }
                if (!same) { return klibDamaged(stringOf("its body does not hash to what its header says")); }
            }
            going = false;
        }
        else { m.bad(format("a header line, found `{}`", w)); }
    }
    if (!m.ok()) { return klibDamaged(format("its header is malformed: {}", m.why)); }
    return klibUsable();
}

// A cached `.klib` checked as a build trusts it: an archive every member of which is whole, whose
// metadata's header and body hold together (`readKlibHead`). The object is measured, not read.
pub checkKlib path:str -> KlibCheck {
    st: Result<Metadata, long> = metadata(path);
    size: long = 0;
    match st {
        Ok(md) { size = md.size; }
        Err(e) { return KlibCheck { ok: false, why: format("cannot be read (errno {})", e) }; }
    }
    f: Result<File, long> = File.openRead(path);
    match f {
        Err(e) { return KlibCheck { ok: false, why: format("cannot be read (errno {})", e) }; }
        Ok(file) {
            meta: String;
            c: KlibCheck = walkArchive(&file, size, &meta);
            file.close();
            if (!c.ok) { return c; }
            h: KlibHead = klibHeadOf();
            v: str = "";
            unsafe { v = meta.view(); }
            return readKlibHead(v, &h);
        }
    }
    return klibUsable();
}

// Every member of the archive `f` (`size` bytes) whole, and the metadata member's bytes into
// `meta`. An `ar` archive is an 8-byte magic, then per member a 60-byte header (the name in its
// first 16 bytes, the decimal size at 48) and the data, padded to an even length.
local walkArchive inout f:File size:long inout meta:String -> KlibCheck {
    head: [u8; 60];
    n: long = 0;
    unsafe { n = f.readInto(&head, 8); }
    if (n != 8 || !(asText(head[0..8]) == "!<arch>\n")) { return klibDamaged(stringOf("it is not an archive")); }
    at: long = 8;
    found: bool = false;
    while (at < size) {
        f.seek(at, Seek.Set);
        unsafe { n = f.readInto(&head, 60); }
        if (n != 60) { return klibDamaged(format("it is cut short at {} bytes, inside a member's header", size)); }
        msize: long = 0;
        k: long = 48;
        while (k < 58 && head[k] >= '0' && head[k] <= '9') { msize = msize * 10 + (head[k] as long) - '0'; k = k + 1; }
        name: str = memberName(asText(head[0..16]));
        if (at + 60 + msize > size) {
            return klibDamaged(format("it is cut short: member `{}` holds {} bytes, of which {} are there", name, msize, size - at - 60));
        }
        if (name == KLIB_META) {
            meta.reserve(msize);
            got: long = 0;
            unsafe { got = f.readInto(meta.buf as long, msize); }
            if (got != msize) { return KlibCheck { ok: false, why: format("cannot be read (only {} of its metadata's {} bytes)", got, msize) }; }
            meta.len = msize;
            found = true;
        }
        at = at + 60 + msize + (msize & 1);
    }
    if (!found) { return klibDamaged(stringOf("it has no `kiln.meta` member")); }
    return klibUsable();
}

// A member's name as `ar` pads it: blanks after, and a `/` ending it in the GNU format.
local memberName raw:str -> str {
    n: long = raw.len;
    while (n > 0 && charAt(raw, n - 1) == ' ') { n = n - 1; }
    if (n > 0 && charAt(raw, n - 1) == '/') { n = n - 1; }
    return strSlice(raw, 0, n);
}

// What a build needs to know before trusting a cached `.klib`: that its format is this one, its
// key, whether it holds the program's entry point, and which files beyond its root directory's
// own the compile read (a module in a subdirectory that one of them includes), whose bytes are
// in the key too. All in the header, ahead of the modules. A file that is missing, damaged or of
// another format answers `ok: false`, and is rebuilt; `present` and `why` say whether there was
// one, and what is wrong with it.
pub struct KlibHeader { ok: bool, present: bool, why: String, key: String, entry: bool, extras: Vec<str> }

pub readKlibHeader path:str -> KlibHeader {
    out: KlibHeader = KlibHeader { ok: false, present: fileExists(path), why: stringOf(""), key: stringOf(""),
                                   entry: false, extras: vec![] };
    if (!out.present) { return out; }
    // The header is the first thing in the member, and a few hundred bytes long.
    meta: Result<String, long> = readKlibMetaUpTo(path, 65536);
    match meta {
        Err(e) { u: KlibCheck = klibUnreadable(e); out.why = u.why; return out; }
        Ok(text) {
            v: str = "";
            unsafe { v = text.view(); }
            m: MetaIn = metaIn(v);
            f: KlibCheck = formatCheck(m.restOfLine());
            if (!f.ok) { out.why = f.why; return out; }
            going: bool = true;
            while (going) {
                if (m.atEnd()) { m.bad(stringOf("`entry`")); going = false; continue; }
                w: str = m.word();
                if (w == "package" || w == "dep") { m.text0(); if (w == "dep") { m.word(); } }
                else if (w == "key") { out.key.pushStr(m.word()); }
                else if (w == "extra") { out.extras.push(keep(m.text0())); }
                else if (w == "init") { m.name(); }
                else if (w == "entry") { out.entry = m.num() != 0; going = false; }
                else { m.bad(format("a header line, found `{}`", w)); }
            }
            if (!m.ok()) { u: KlibCheck = klibDamaged(format("its header is malformed: {}", m.why)); out.why = u.why; return out; }
            if (out.key.length() == 0) { u: KlibCheck = klibDamaged(stringOf("its header has no key")); out.why = u.why; return out; }
            out.ok = true;
            return out;
        }
    }
    return out;
}

// ─── the key ─────────────────────────────────────────────────────────────────

// A package's key: a 128-bit hash of everything its `.klib` is made from, by content. The
// compiler that builds it, the package's name and manifest, every source file it compiled (path
// and bytes, in path order: the path is in its diagnostics and bounds messages), and the keys of
// its direct dependencies (in name order), which is how a change anywhere below reaches every
// package above it. The build driver computes it to decide what is current; the compile computes
// it from the files it actually read and writes it into the metadata.
pub klibKey compilerId:str name:str manifest:str sources:Vec<str> deps:Vec<KlibDep> -> String {
    h: Hasher128;
    h.updateStr("kiln-klib-key 1\ncompiler ");
    h.updateStr(compilerId);
    h.updateStr("\npackage ");
    h.updateStr(name);
    h.updateStr("\n");
    hashFile(&h, manifest);
    srcs: Vec<str>;
    srcs.extend(sources);
    sort(&srcs);
    for src in srcs { hashFile(&h, src); }
    names: Vec<str>;
    for dep in deps { names.push(dep.name); }
    sort(&names);
    for depName in names {
        for d in deps {
            if (d.name == depName) {
                h.updateStr("dep ");
                h.updateStr(d.name);
                h.updateStr(" ");
                h.updateStr(d.key);
                h.updateStr("\n");
            }
        }
    }
    r: Hash128 = h.finish();
    return r.hex();
}

// A file into a key: its path, its length, its bytes. One that cannot be read keys as missing,
// which no file's content can collide with.
local hashFile inout h:Hasher128 path:str -> void {
    h.updateStr("file ");
    h.updateStr(path);
    body: Result<String, long> = readFileString(path);
    match body {
        Ok(b) {
            lenText: String = format(" {}\n", b.length());
            unsafe { h.updateStr(lenText.view()); h.updateStr(b.view()); }
        }
        Err(_) { h.updateStr(" missing\n"); }
    }
}

// The compiler's own identity, for every key it builds: the hash of its executable.
pub compilerIdentity -> str {
    exe: Result<String, long> = readFileString("/proc/self/exe");
    match exe {
        Ok(bytes) {
            h: Hash128;
            unsafe { h = hash128Str(bytes.view()); }
            v: str = "";
            v = keepString(h.hex());
            return v;
        }
        Err(e) { failStr(format("cannot read the compiler's own executable (errno {})", e)); }
    }
    return "";
}

// ─── loading one into this compile ───────────────────────────────────────────

// `--extern name=path`: read the `.klib` for package `name` and make everything in it known:
// its modules to the scanner (each read into the tree when the scan reaches it,
// `KlibTree.loadModuleSection`), its exports to the emitter (as externs), its facts to the
// middle end, and the package itself as upstream.
pub loadKlib name:str path:str -> void {
    meta: Result<String, long> = readKlibMeta(path);
    text: str = "";
    match meta {
        Ok(t)  { text = holdSource(t); }
        Err(e) { cannotUse(name, path, klibUnreadable(e)); }
    }
    h: KlibHead = klibHeadOf();
    c: KlibCheck = readKlibHead(text, &h);
    if (!c.ok) { cannotUse(name, path, c); }
    if (!(h.name == name)) {
        failStr(format("`{}` holds package `{}`, not `{}`", path, h.name, name));
    }
    info: KlibInfo = KlibInfo { name: h.name, key: h.key, path: keep(path), init: h.init, entry: h.entry,
                                firstDep: gKlibDeps.len(), depCount: h.deps.len(),
                                body: h.body, symBase: gSymIn.len(), symCount: 0,
                                imageBase: gFacts.images.len(), modulesAt: 0 };
    gKlibDeps.extend(h.deps);
    b: KlibCheck = readKlibBody(&info, gKlibs.len());
    if (!b.ok) { cannotUse(name, path, b); }
    gUpstreamPkgs.put(info.name, true);
    gKlibs.push(info);
}

// The package-wide chunks of a body: names, exports, instances, the facts that are not per
// module, and the module directory. A module's own section is read when the scan reaches it.
local readKlibBody inout info:KlibInfo index:long -> KlibCheck {
    d: Decoder;
    unsafe { d = decoderOf(info.body as [u8]); }
    while (d.remaining() > 0 && d.ok()) {
        tag: long = d.getUvarint() as long;
        n: long = d.getLen();
        at: long = d.pos;
        c: Decoder;
        unsafe { c = decoderOf(d.getRaw(n)); }
        if (tag == CHUNK_STRINGS) {
            // The names: their spellings are views of the body, interned only when first read.
            count: long = c.getLen();
            lens: Vec<long>;
            lens.reserve(count);
            for k in 0..count { lens.push(c.getLen()); }
            for len in lens {
                gSymInText.push(c.getRaw(len) as str);
                gSymIn.push(SYM_UNREAD);
            }
            info.symCount = count;
            gSymInBase = info.symBase;
            gSymInCount = count;
        } else if (tag == CHUNK_EXPORTS) {
            k: long = c.getLen();
            while (k > 0 && c.ok()) { gUseSyms.put(c.getStr(), true); k = k - 1; }
        } else if (tag == CHUNK_STAMPED) {
            k: long = c.getLen();
            while (k > 0 && c.ok()) { gKnownInstances.put(c.getStr(), true); k = k - 1; }
        } else if (tag == CHUNK_INSTFNS) {
            // What this package compiled of the instances: linked to by a dependent that makes
            // the same instance against the same implementations (`Mono.reuseOf`).
            k: long = c.getLen();
            while (k > 0 && c.ok()) {
                name: Sym = Sym.decode(c);
                alias: Sym = Sym.decode(c);
                fp: long = c.getVarint();
                fact: long = getFnFact(&c);
                addInstExport(InstExport { name: name, alias: alias, fp: fp, fact: fact, klib: index, next: -1 });
                gUseSyms.put(nameOf(alias), true);
                k = k - 1;
            }
        } else if (tag == CHUNK_IR) {
            readShipChunk(&c, info.symBase, info.symCount);
        } else if (tag == CHUNK_EFFECTS) {
            readEffectsChunk(&c);
        } else if (tag == CHUNK_POISON) {
            if (bool.decode(c)) { gFacts.poisonAll = true; }
            k: long = c.getLen();
            while (k > 0 && c.ok()) { gFacts.addPoison(Sym.decode(c)); k = k - 1; }
        } else if (tag == CHUNK_IMAGES) {
            k: long = c.getLen();
            while (k > 0 && c.ok()) {
                isBlock: bool = bool.decode(c);
                bytes: [u8] = c.getBytes();
                firstByte: long = gFacts.bytes.len();
                gFacts.bytes.extendSlice(bytes);
                nr: long = c.getLen();
                firstReloc: long = gFacts.relocs.len();
                j: long = 0;
                while (j < nr && c.ok()) {
                    r: RelocFact = RelocFact.decode(c);
                    img: long = r.image;
                    if (img >= 0) { img = img + info.imageBase; }
                    gFacts.relocs.push(RelocFact { offset: r.offset, kind: r.kind, target: r.target, image: img,
                                                   delta: r.delta, concrete: r.concrete, trait: r.trait });
                    j = j + 1;
                }
                gFacts.images.push(ImgFact { firstByte: firstByte, byteCount: bytes.len, firstReloc: firstReloc,
                                             relocCount: nr, isBlock: isBlock });
                k = k - 1;
            }
        } else if (tag == CHUNK_MODDIR) {
            k: long = c.getLen();
            while (k > 0 && c.ok()) {
                r: ModRec = ModRec.decode(c);
                firstInc: long = gKlibIncludes.len();
                gKlibIncludes.extend(r.includes);
                gKlibModuleAt.put(r.path, gKlibModules.len());
                gKlibModules.push(KlibModule { path: r.path, pkg: r.pkg, firstInclude: firstInc,
                                               includeCount: r.includes.len(), hasMacro: r.hasMacro,
                                               klib: index, at: r.at, len: r.len });
                gProvidedPaths.put(r.path, true);
                k = k - 1;
            }
        } else if (tag == CHUNK_MODULES) {
            info.modulesAt = at;
        }
        if (!c.ok()) { return klibDamaged(format("its metadata is malformed: {}", c.error())); }
    }
    if (!d.ok()) { return klibDamaged(format("its metadata is malformed: {}", d.error())); }
    return klibUsable();
}

// Every loaded `.klib` was built against the dependencies it names; the ones loaded beside it
// must be those very builds. A mismatch is a stale archive, and trusting it would link code
// compiled against declarations that have since changed. A build never hands a compile one,
// since the dependencies' keys are in its own key; a compile handed one stops on it.
pub checkKlibConsistency -> void {
    for info in gKlibs {
        for k in 0..info.depCount {
            d: KlibDep = gKlibDeps.get(info.firstDep + k);
            at: long = klibIndex(d.name);
            if (at < 0) {
                failStr(format("`{}` depends on package `{}`, which no `--extern` provides", info.path, d.name));
            }
            c: KlibCheck = staleCheck(d, gKlibs.get(at));
            if (!c.ok) { cannotUse(info.name, info.path, c); }
        }
    }
}
// Whether the dependency `d` a `.klib` records is the build `have` loaded beside it.
local staleCheck d:KlibDep have:KlibInfo -> KlibCheck {
    if (have.key == d.key) { return klibUsable(); }
    return KlibCheck { ok: false, why: format("is stale (built against package `{}` with key {}, but `{}` has key {})",
                                              d.name, d.key, have.path, have.key) };
}

// One function's facts (`gOutFacts` entry `fi`), written the way a module section's FACTS and
// INSTFNS carry them, and read back into `gFacts`, answering the new entry.
pub putFnFact inout out:Encoder fi:long -> void {
    f: FnFact = gOutFacts.fns.get(fi);
    f.divergent.encode(out);
    f.writes.encode(out);
    f.retKind.encode(out);
    f.retStruct.encode(out);
    out.putLen(f.paramCount);
    for j in 0..f.paramCount { pf: ParamFact = gOutFacts.paramAt(f, j); pf.encode(out); }
    out.putLen(f.depCount);
    for j in 0..f.depCount { df: DepFact = gOutFacts.depAt(f, j); df.encode(out); }
}
pub getFnFact inout d:Decoder -> long {
    div: bool = bool.decode(d);
    writes: long = d.getVarint();
    rk: Lit = Lit.decode(d);
    rs: Sym = Sym.decode(d);
    ps: Vec<ParamFact>;
    n: long = d.getLen();
    for k in 0..n { ps.push(ParamFact.decode(d)); }
    ds: Vec<DepFact>;
    n = d.getLen();
    for k in 0..n { ds.push(DepFact.decode(d)); }
    return gFacts.addFn(FnFact { divergent: div, writes: writes, retKind: rk, retStruct: rs,
                                 firstParam: 0, paramCount: 0, firstDep: 0, depCount: 0 }, ps, ds);
}

pub klibIndex name:str -> long {
    for i in 0..gKlibs.len() {
        if (gKlibs.get(i).name == name) { return i; }
    }
    return -1;
}

// The loaded packages in dependency order (each after everything it depends on): the order their
// startup initializers run in.
pub klibOrder -> Vec<long> {
    out: Vec<long>;
    seen: Vec<bool>;
    for i in 0..gKlibs.len() { seen.push(false); }
    for i in 0..gKlibs.len() { visitKlib(i, &seen, &out); }
    return out;
}
// Each loaded package's place in that order, for the facts: an instance two dependencies both
// compiled is linked to the lower one's (`instExportFor`).
pub rankKlibs -> void {
    order: Vec<long> = klibOrder();
    gKlibRank.clear();
    for i in 0..gKlibs.len() { gKlibRank.push(0); }
    for pos in 0..order.len() { gKlibRank.set(order.get(pos), pos); }
}
local visitKlib i:long inout seen:Vec<bool> inout out:Vec<long> -> void {
    if (seen.get(i)) { return; }
    seen.set(i, true);
    info: KlibInfo = gKlibs.get(i);
    for k in 0..info.depCount {
        at: long = klibIndex(gKlibDeps.get(info.firstDep + k).name);
        if (at >= 0) { visitKlib(at, seen, out); }
    }
    out.push(i);
}

pub klibModule path:str -> long {
    hit: Option<long> = gKlibModuleAt.find(path);
    match hit { Some(i) { return i; } None { } }
    return -1;
}
