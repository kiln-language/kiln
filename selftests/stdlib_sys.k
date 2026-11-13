// File metadata and file operations, child processes with pipes, random numbers, and thread
// stacks with a guard page. Exits 0 when every check holds, otherwise the number of the first
// that did not. Run with the argument `overflow`, it overflows a thread's stack (the parent
// checks that this ends in SIGSEGV at the guard page).
#include <stdlib::{io, file, dir, process, random, string, vec, time, thread, textfile}>

deep n:long -> long { pad: [long; 64]; pad[0] = n; if (n == 0) { return 0; } return deep(n - 1) + pad[0] - n + 1; }
overflowBody ctrl:long -> void { deep(1000000); }

main args: ...str -> int {
    if (args.len > 1 && strEq(args[1], "overflow")) {
        t: Thread = spawnWithStack(&overflowBody, 0, 16384);
        t.join();
        return 0;                          // not reached: the guard page stops it first
    }

    // metadata
    path: str = "/tmp/kiln_selftest_sys.txt";
    writeFileStr(path, "twelve bytes").unwrap();
    m: Metadata = metadata(path).unwrap();
    if (m.len() != 12 || !m.isFile() || m.isDir() || m.isSymlink()) { return 1; }
    if (m.modifiedNs / 1000000000 < 1700000000 || m.nlink < 1) { return 2; }
    f: File = File.openRead(path).unwrap();
    if (f.size() != 12 || f.metadata().unwrap().ino != m.ino) { return 3; }
    if (!metadata("/tmp").unwrap().isDir() || metadata("/no/such/file").unwrapErr() != Errno.NoEnt) { return 4; }
    if (!symlinkMetadata("/proc/self/exe").unwrap().isSymlink() || symlinkMetadata("/proc/self/exe").unwrap().isFile()) { return 5; }
    if (!metadata("/proc/self/exe").unwrap().isFile()) { return 6; }        // followed

    // positional I/O, length, permissions, copy, links
    g: File = File.openReadWrite(path).unwrap();
    four: [u8; 4];
    if (g.readAt(&four[..], 3) != 4 || four[..] as str != "lve " || g.writeAt("XY" as [u8], 10) != 2) { return 9; }
    g.setLen(14).unwrap();
    g.setPermissions(0x180).unwrap();                                    // 0o600
    g.syncData().unwrap();
    copy: str = "/tmp/kiln_selftest_sys.copy";
    if (copyFile(path, copy).unwrap() != 14 || metadata(copy).unwrap().permissions() != 0x180) { return 10; }
    text: String = readFileString(copy).unwrap();
    if (text.length() != 14 || !text.startsWith("twelve bytXY")) { return 11; }
    link: str = "/tmp/kiln_selftest_sys.link";
    removeFile(link).isOk();
    softLink(path, link).unwrap();
    if (readLink(link).unwrap() != path || !symlinkMetadata(link).unwrap().isSymlink()) { return 12; }
    hard: str = "/tmp/kiln_selftest_sys.hard";
    removeFile(hard).isOk();
    hardLink(path, hard).unwrap();
    if (metadata(path).unwrap().nlink != 2) { return 13; }
    setPermissions(copy, 0x1A4).unwrap();                               // 0o644
    if (metadata(copy).unwrap().permissions() != 0x1A4) { return 14; }
    removeFile(link).unwrap(); removeFile(hard).unwrap(); removeFile(copy).unwrap();
    removeFile(path).unwrap();

    // threads: a pool size, and a stack overflow that ends at the guard page
    if (availableParallelism() < 1) { return 15; }
    crashed: ExitStatus = Command.of("/proc/self/exe").arg("overflow").status().unwrap();
    if (crashed.signal().unwrapOr(0) != 11) { return 16; }                // SIGSEGV

    // a directory listing knows every entry's kind
    d: Dir = openDir("/proc/self").unwrap();
    sawDir: bool = false;
    loop {
        o: Option<DirEntry> = d.nextReal();
        match o {
            Some(e) {
                if (e.kind() == EntryKind.Unknown) { return 7; }
                if (e.isDir()) { sawDir = true; }
            }
            None { break; }
        }
    }
    if (!sawDir) { return 8; }

    // processes: captured output, piped input, environment, directory, status
    o: Output = Command.of("sh").arg("-c").arg("echo out; echo err >&2; exit 3").output().unwrap();
    if (o.stdout != "out\n" || o.stderr != "err\n" || o.status.code().unwrapOr(-1) != 3) { return 20; }
    c: Child = Command.of("tr").arg("a-z").arg("A-Z").stdin(Stdio.Piped).stdout(Stdio.Piped).spawn().unwrap();
    { w: File = c.stdin.take().unwrap(); w.writeStr("piped\n"); }
    r: Output = c.waitWithOutput().unwrap();
    if (r.stdout != "PIPED\n" || !r.status.success()) { return 21; }
    e: Output = Command.of("sh").arg("-c").arg("echo $KX-$HOME; pwd").envClear().env("KX", "yes").currentDir("/tmp").output().unwrap();
    if (e.stdout != "yes-\n/tmp\n") { return 22; }
    if (!Command.of("true").status().unwrap().success()) { return 23; }
    if (Command.of("no-such-program-xyz").output().unwrapErr() != Errno.NoEnt) { return 24; }
    big: Output = Command.of("sh").arg("-c").arg("head -c 200000 /dev/zero; head -c 100000 /dev/zero >&2").output().unwrap();
    if (big.stdout.length() != 200000 || big.stderr.length() != 100000) { return 25; }   // both pipes drained
    q: Output = Command.of("cat").stdout(Stdio.Null).output().unwrap();               // stdin from nothing
    if (q.stdout.length() != 0 || !q.status.success()) { return 26; }
    k: Child = Command.of("sleep").arg("10").spawn().unwrap();
    k.kill().unwrap();
    if (k.wait().unwrap().signal().unwrapOr(0) != 9) { return 27; }

    // random
    a: Rng = Rng.seeded(42);
    if (a.next() != 1546998764402558742 || a.next() != 6990951692964543102) { return 40; }
    b: Rng = Rng.seeded(7);
    for i in 0..1000 {
        x: long = b.range(-3, 4);
        if (x < -3 || x >= 4) { return 41; }
    }
    if (randomU64() == randomU64()) { return 42; }
    v: Vec<long>;
    for i in 0..50 { v.push(i); }
    s: Rng = Rng.seeded(1);
    shuffle(&v, &s);
    sum: long = 0;
    moved: long = 0;
    for i in 0..50 { sum = sum + v.get(i); if (v.get(i) != i) { moved = moved + 1; } }
    if (sum != 1225 || moved < 25) { return 43; }
    return 0;
}
