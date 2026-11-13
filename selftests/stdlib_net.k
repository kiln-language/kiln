// stdlib net.k: addresses parsed, printed, compared; TCP and UDP over loopback in one process.
// Exits 0 when every check holds, otherwise the number of the first one that did not.
#include <stdlib::io>
#include <stdlib::net>
#include <stdlib::poll>
#include <stdlib::string>
#include <stdlib::map>

shown4 s:str -> String {
    r: Result<Ipv4Addr, AddrParseError> = Ipv4Addr.parse(s);
    match r { Ok(a) { return format("{}", a); } Err(e) { return format("{}", e); } }
}
shown6 s:str -> String {
    r: Result<Ipv6Addr, AddrParseError> = Ipv6Addr.parse(s);
    match r { Ok(a) { return format("{}", a); } Err(e) { return format("{}", e); } }
}
shownSock s:str -> String {
    r: Result<SocketAddr, AddrParseError> = SocketAddr.parse(s);
    match r { Ok(a) { return format("{}", a); } Err(e) { return format("{}", e); } }
}

main -> int {
    // IPv4
    if (shown4("192.168.1.20") != "192.168.1.20") { return 1; }
    if (shown4("256.1.1.1") != "invalid IPv4 address syntax") { return 2; }
    if (shown4("1.2.3") != "invalid IPv4 address syntax" || shown4("01.2.3.4") != "invalid IPv4 address syntax") { return 3; }
    lo: Ipv4Addr = Ipv4Addr.localhost();
    if (!lo.isLoopback() || lo.octet(0) != 127 || !Ipv4Addr.of(10, 1, 2, 3).isPrivate() || Ipv4Addr.of(8, 8, 8, 8).isPrivate()) { return 4; }
    if (!(Ipv4Addr.of(1, 2, 3, 4) < Ipv4Addr.of(1, 2, 3, 5)) || Ipv4Addr.of(1, 2, 3, 4) != Ipv4Addr.parse("1.2.3.4").unwrap()) { return 5; }

    // IPv6, printed the RFC 5952 way
    if (shown6("2001:0db8:0000:0000:0000:0000:0000:0001") != "2001:db8::1") { return 10; }
    if (shown6("::") != "::" || shown6("::1") != "::1" || shown6("1::") != "1::") { return 11; }
    if (shown6("1:0:0:2:0:0:0:3") != "1:0:0:2::3") { return 12; }                 // the longer run
    if (shown6("1:0:2:3:4:5:6:7") != "1:0:2:3:4:5:6:7") { return 13; }             // one zero stays
    if (shown6("::ffff:10.0.0.1") != "::ffff:10.0.0.1") { return 14; }
    if (shown6("1:2:3:4:5:6:7:8:9") != "invalid IPv6 address syntax" || shown6("1::2::3") != "invalid IPv6 address syntax") { return 15; }
    if (shown6("12345::") != "invalid IPv6 address syntax" || shown6("1:2:3:4:5:6:7") != "invalid IPv6 address syntax") { return 16; }
    m: Option<Ipv4Addr> = Ipv6Addr.parse("::ffff:1.2.3.4").unwrap().toIpv4Mapped();
    if (m.unwrap().octet(3) != 4 || !Ipv6Addr.localhost().isLoopback() || !Ipv6Addr.parse("fe80::1").unwrap().isUnicastLinkLocal()) { return 17; }

    // IpAddr / SocketAddr
    ip: IpAddr = IpAddr.parse("::1").unwrap();
    if (!ip.isIpv6() || !ip.isLoopback() || IpAddr.parse("10.0.0.1").unwrap() != IpAddr.V4(Ipv4Addr.of(10, 0, 0, 1))) { return 20; }
    if (IpAddr.parse("10.0.0.1").unwrap() == IpAddr.parse("::ffff:10.0.0.1").unwrap()) { return 21; }
    if (IpAddr.parse("::ffff:10.0.0.1").unwrap().toCanonical() != IpAddr.parse("10.0.0.1").unwrap()) { return 22; }
    if (shownSock("127.0.0.1:8080") != "127.0.0.1:8080" || shownSock("[::1]:443") != "[::1]:443") { return 23; }
    if (shownSock("[fe80::1%3]:22") != "[fe80::1%3]:22" || shownSock("1.2.3.4:65536") != "invalid socket address syntax") { return 24; }
    sa: SocketAddr = SocketAddr.parse("10.1.1.1:80").unwrap();
    if (sa.port() != 80 || sa.withPort(81).port() != 81 || sa == sa.withPort(81) || !(sa < sa.withPort(81))) { return 25; }
    seen: HashMap<SocketAddr, long>;
    seen.put(sa, 1);
    if (seen.getOr(SocketAddr.parse("10.1.1.1:80").unwrap(), 0) != 1 || seen.getOr(sa.withPort(9), 0) != 0) { return 26; }
    padded: String = format("[{:>16}]", sa);
    if (padded != "[     10.1.1.1:80]") { return 27; }

    // resolution: numeric, localhost, and an error for nonsense
    all: Vec<SocketAddr> = "localhost:80".toSocketAddrs().unwrap();
    if (all.len() < 1 || !all.get(0).ip().isLoopback()) { return 30; }
    if ("no-such-host.invalid:80".toSocketAddrs().isOk() || "missing-port".toSocketAddrs().isOk()) { return 31; }

    // TCP over loopback: bind an ephemeral port, connect (the backlog completes it), accept
    l: TcpListener = TcpListener.bind("127.0.0.1:0").unwrap();                 // any ToSocketAddrs
    at: SocketAddr = l.localAddr().unwrap();
    if (at.port() == 0 || !at.ip().isLoopback()) { return 40; }
    c: TcpStream = TcpStream.connect(at).unwrap();
    s, from = l.accept().unwrap();                     // Rust's (TcpStream, SocketAddr)
    if (from != c.localAddr().unwrap() || s.peerAddr().unwrap() != c.localAddr().unwrap()) { return 41; }
    if (c.writeStr("ping") != 4) { return 42; }
    buf: [u8; 16];
    if (s.peek(&buf[..]) != 4 || s.readExact(&buf[..4]).unwrap() != 4 || buf[..4] as str != "ping") { return 43; }
    writeTo(s, "pong {}", 7);
    s.shutdown(Shutdown.Write).unwrap();
    got: String = c.readToString().unwrap();
    if (got != "pong 7") { return 44; }
    c.setNodelay(true).unwrap();
    c.setReadTimeout(Option.Some(250000000)).unwrap();
    if (!c.nodelay().unwrap() || c.readTimeout().unwrap().unwrapOr(0) < 200000000) { return 45; }
    if (c.ttl().unwrap() <= 0 || c.takeError().unwrap().isSome()) { return 46; }
    c2: TcpStream = c.tryClone().unwrap();
    if (c2.rawFd() == c.rawFd() || c2.peerAddr().unwrap() != at) { return 47; }
    raw: long = c2.intoRawFd();                          // c2 gives the descriptor up...
    c3: TcpStream;
    unsafe { c3 = TcpStream.fromRawFd(raw); }           // ...and c3 takes it over
    if (raw < 0 || c3.peerAddr().unwrap() != at) { return 49; }
    if (c.setReadTimeout(Option.Some(0)).isOk()) { return 48; }

    // a refused connection, and a timed-out read on a non-blocking stream
    l.setNonblocking(true).unwrap();
    if (l.accept().unwrapErr() != Errno.Again) { return 50; }
    gone: TcpListener = TcpListener.bind("127.0.0.1:0").unwrap();
    deadAt: SocketAddr = gone.localAddr().unwrap();
    gone.close();
    if (TcpStream.connect(deadAt).unwrapErr() != Errno.ConnRefused) { return 51; }

    // UDP over loopback, both directions
    a: UdpSocket = UdpSocket.bind("127.0.0.1:0").unwrap();
    b: UdpSocket = UdpSocket.bind("127.0.0.1:0").unwrap();
    bAt: SocketAddr = b.localAddr().unwrap();
    if (a.sendTo("hello" as [u8], bAt).unwrap() != 5) { return 60; }
    got5, sender = b.recvFrom(&buf[..]).unwrap();      // Rust's (usize, SocketAddr)
    if (got5 != 5 || buf[..5] as str != "hello" || sender != a.localAddr().unwrap()) { return 61; }
    b.connect(sender).unwrap();
    b.send("back" as [u8]).unwrap();
    n: long = a.recv(&buf[..]).unwrap();
    if (n != 4 || buf[..4] as str != "back" || b.peerAddr().unwrap() != a.localAddr().unwrap()) { return 62; }
    b.setBroadcast(true).unwrap();
    if (!b.broadcast().unwrap()) { return 63; }

    // poll.k: readiness of a listener, a connection's data, writability, a hangup, a timeout
    pl: TcpListener = TcpListener.bind("127.0.0.1:0").unwrap();
    pat: SocketAddr = pl.localAddr().unwrap();
    p: Poller = Poller.open().unwrap();
    p.add(pl.rawFd(), Interest.Readable).unwrap();
    ready: Vec<Event>;
    if (p.wait(&ready, Option.Some(20000000)).unwrap() != 0 || ready.len() != 0) { return 70; }   // nothing yet
    pc: TcpStream = TcpStream.connect(pat).unwrap();
    if (p.wait(&ready, Option.Some(1000000000)).unwrap() != 1 || ready.get(0).fd != pl.rawFd() || !ready.get(0).readable()) { return 71; }
    ps, ppeer = pl.accept().unwrap();
    p.add(ps.rawFd(), Interest.Readable).unwrap();
    pc.writeStr("hi");
    p.wait(&ready, Option.Some(1000000000)).unwrap();
    sawData: bool = false;
    for ev in ready { if (ev.fd == ps.rawFd() && ev.readable()) { sawData = true; } }
    if (!sawData) { return 72; }
    p.modify(ps.rawFd(), Interest.Writable).unwrap();
    if (p.wait(&ready, Option.Some(1000000000)).unwrap() != 1 || !ready.get(0).writable() || ready.get(0).readable()) { return 73; }
    p.modify(ps.rawFd(), Interest.Readable).unwrap();
    pc.close();
    p.wait(&ready, Option.Some(1000000000)).unwrap();
    if (ready.len() != 1 || !ready.get(0).hangup()) { return 74; }
    p.remove(ps.rawFd()).unwrap();
    p.remove(pl.rawFd()).unwrap();
    if (p.wait(&ready, Option.Some(20000000)).unwrap() != 0) { return 75; }
    q: Poller = Poller.open().unwrap();                 // a second poller sharing the listener
    p.addExclusive(pl.rawFd(), Interest.Readable).unwrap();
    q.addExclusive(pl.rawFd(), Interest.Readable).unwrap();
    pc2: TcpStream = TcpStream.connect(pat).unwrap();
    if (p.wait(&ready, Option.Some(1000000000)).unwrap() != 1 || ready.get(0).fd != pl.rawFd()) { return 76; }
    return 0;
}
