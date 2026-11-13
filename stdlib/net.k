// TCP and UDP over IPv4 and IPv6, after Rust's std::net. Errors are Result<_, long> with a
// positive errno; Read/Write answer a count or a negative errno. No DNS: numeric addresses,
// localhost and /etc/hosts only.
#include <{core, sys, option, result, vec, string, chars, fmt, cmp, textfile, iter}>

pub NS_PER_SECOND: long = 1000000000;

local SOCKADDR_MAX: long = 28;
local DEFAULT_BACKLOG: long = 128;

local enum Family: long   { Inet = 2, Inet6 = 10 }
local enum SockType: long { Stream = 1, Dgram = 2, CloExec = 0x80000 }
local enum Level: long    { Ip = 0, Socket = 1, Tcp = 6, Ipv6 = 41 }
local enum SockOpt: long  { ReuseAddr = 2, Error = 4, Broadcast = 6, RecvTimeout = 20, SendTimeout = 21 }
local enum ProtoOpt: long { TcpNoDelay = 1, IpTtl = 2, Ipv6Hops = 16 }
local enum MsgFlag: long  { Peek = 2, NoSignal = 0x4000 }
local POLLOUT: long = 4;
local F_DUPFD_CLOEXEC: long = 1030;
local FIONBIO: long = 0x5421;

pub struct Ipv4Addr { bits: u32 }
pub enum AddrParseError: long { Ip = 0, Ipv4 = 1, Ipv6 = 2, Socket = 3, SocketV4 = 4, SocketV6 = 5 }
pub struct Ipv6Addr { hi: u64, lo: u64 }

methods Ipv4Addr for Default { new -> Ipv4Addr { return Ipv4Addr { bits: 0 }; } }

methods Ipv4Addr {
    parse s:str -> Result<Ipv4Addr, AddrParseError> { return parseIpv4(s); }
    of a:long b:long c:long d:long -> Ipv4Addr {
        return Ipv4Addr { bits: (((a & 255) << 24) | ((b & 255) << 16) | ((c & 255) << 8) | (d & 255)) as u32 };
    }
    fromBits bits:u32 -> Ipv4Addr { return Ipv4Addr { bits: bits }; }
    localhost   -> Ipv4Addr { return Ipv4Addr.of(127, 0, 0, 1); }
    unspecified -> Ipv4Addr { return Ipv4Addr { bits: 0 }; }
    broadcast   -> Ipv4Addr { return Ipv4Addr.of(255, 255, 255, 255); }

    octet &self i:long -> long { return ((self.bits as long) >> (24 - 8 * i)) & 255; }
    toBits &self -> u32 { return self.bits; }

    isUnspecified &self -> bool { return self.bits == 0; }
    isLoopback    &self -> bool { return self.octet(0) == 127; }
    isPrivate     &self -> bool {
        a: long = self.octet(0);
        b: long = self.octet(1);
        return a == 10 || (a == 172 && b >= 16 && b < 32) || (a == 192 && b == 168);
    }
    isLinkLocal   &self -> bool { return self.octet(0) == 169 && self.octet(1) == 254; }
    isMulticast   &self -> bool { return self.octet(0) >= 224 && self.octet(0) < 240; }
    isBroadcast   &self -> bool { return self.bits == Ipv4Addr.broadcast().bits; }
    isDocumentation &self -> bool {
        a: long = self.octet(0); b: long = self.octet(1); c: long = self.octet(2);
        return (a == 192 && b == 0 && c == 2) || (a == 198 && b == 51 && c == 100) || (a == 203 && b == 0 && c == 113);
    }
    toIpv6Mapped     &self -> Ipv6Addr { return Ipv6Addr { hi: 0, lo: ((0xffff as u64) << 32) | (self.bits as u64) }; }
    toIpv6Compatible &self -> Ipv6Addr { return Ipv6Addr { hi: 0, lo: self.bits as u64 }; }
}

methods Ipv4Addr for Display {
    display &self w:Write -> void {
        for i in 0..4 {
            if (i > 0) { putStr(w, "."); }
            putLong(w, self.octet(i));
        }
    }
}
methods Ipv4Addr for Ord {
    cmp &self other:Ipv4Addr -> int { return self.bits.cmp(other.bits); }
}
methods Ipv4Addr for Hash {
    hash &self -> u64 { return mixHash(self.bits as u64); }
}

methods Ipv6Addr for Default { new -> Ipv6Addr { return Ipv6Addr { hi: 0, lo: 0 }; } }

methods Ipv6Addr {
    parse s:str -> Result<Ipv6Addr, AddrParseError> { return parseIpv6(s); }
    fromSegments segs:[long] -> Ipv6Addr {
        a: Ipv6Addr = Ipv6Addr { hi: 0, lo: 0 };
        for i in 0..8 {
            v: u64 = 0;
            if (i < segs.len) { v = (segs[i] & 0xffff) as u64; }
            if (i < 4) { a.hi = a.hi | (v << (48 - 16 * i)); }
            else       { a.lo = a.lo | (v << (48 - 16 * (i - 4))); }
        }
        return a;
    }
    fromHalves hi:u64 lo:u64 -> Ipv6Addr { return Ipv6Addr { hi: hi, lo: lo }; }
    localhost   -> Ipv6Addr { return Ipv6Addr { hi: 0, lo: 1 }; }
    unspecified -> Ipv6Addr { return Ipv6Addr { hi: 0, lo: 0 }; }

    segment &self i:long -> long {
        if (i < 4) { return ((self.hi >> (48 - 16 * i)) & 0xffff) as long; }
        return ((self.lo >> (48 - 16 * (i - 4))) & 0xffff) as long;
    }
    octet &self i:long -> long {
        if (i < 8) { return ((self.hi >> (56 - 8 * i)) & 255) as long; }
        return ((self.lo >> (56 - 8 * (i - 8))) & 255) as long;
    }

    isUnspecified &self -> bool { return self.hi == 0 && self.lo == 0; }
    isLoopback    &self -> bool { return self.hi == 0 && self.lo == 1; }
    isMulticast   &self -> bool { return self.segment(0) >= 0xff00; }
    isUniqueLocal &self -> bool { return (self.segment(0) & 0xfe00) == 0xfc00; }
    isUnicastLinkLocal &self -> bool { return (self.segment(0) & 0xffc0) == 0xfe80; }
    isDocumentation &self -> bool { return self.segment(0) == 0x2001 && self.segment(1) == 0xdb8; }

    toIpv4Mapped &self -> Option<Ipv4Addr> {
        if (self.hi == 0 && (self.lo >> 32) == 0xffff) { return Option.Some(Ipv4Addr { bits: (self.lo & 0xffffffff) as u32 }); }
        return Option.None;
    }
    toIpv4 &self -> Option<Ipv4Addr> {
        if (self.hi == 0 && ((self.lo >> 32) == 0xffff || (self.lo >> 32) == 0)) {
            return Option.Some(Ipv4Addr { bits: (self.lo & 0xffffffff) as u32 });
        }
        return Option.None;
    }
}

methods Ipv6Addr for Display {
    display &self w:Write -> void {
        m: Option<Ipv4Addr> = self.toIpv4Mapped();
        match m {
            Some(v4) { putStr(w, "::ffff:"); v4.display(w); return; }
            None {}
        }
        bestAt: long = -1; bestLen: long = 1;
        i: long = 0;
        while (i < 8) {
            if (self.segment(i) == 0) {
                j: long = i;
                while (j < 8 && self.segment(j) == 0) { j = j + 1; }
                if (j - i > bestLen) { bestAt = i; bestLen = j - i; }
                i = j;
            } else { i = i + 1; }
        }
        i = 0;
        while (i < 8) {
            if (i == bestAt) {
                putStr(w, "::");
                i = i + bestLen;
                continue;
            }
            if (i > 0 && i != bestAt + bestLen) { putStr(w, ":"); }
            putHex(w, self.segment(i) as u64);
            i = i + 1;
        }
    }
}
methods Ipv6Addr for Ord {
    cmp &self other:Ipv6Addr -> int {
        if (self.hi != other.hi) { if (self.hi < other.hi) { return -1; } return 1; }
        if (self.lo != other.lo) { if (self.lo < other.lo) { return -1; } return 1; }
        return 0;
    }
}
methods Ipv6Addr for Hash {
    hash &self -> u64 { return combineHash(mixHash(self.hi), self.lo); }
}

pub enum IpAddr { V4(Ipv4Addr), V6(Ipv6Addr) }

methods IpAddr {
    parse s:str -> Result<IpAddr, AddrParseError> { return parseIp(s); }
    isIpv4 &self -> bool { match self { V4(a) { return true; } V6(b) { return false; } } }
    isIpv6 &self -> bool { return !self.isIpv4(); }
    isUnspecified &self -> bool { match self { V4(a) { return a.isUnspecified(); } V6(b) { return b.isUnspecified(); } } }
    isLoopback    &self -> bool { match self { V4(a) { return a.isLoopback(); } V6(b) { return b.isLoopback(); } } }
    isMulticast   &self -> bool { match self { V4(a) { return a.isMulticast(); } V6(b) { return b.isMulticast(); } } }
    toCanonical &self -> IpAddr {
        match self {
            V4(a) { return IpAddr.V4(a); }
            V6(b) {
                m: Option<Ipv4Addr> = b.toIpv4Mapped();
                match m { Some(v4) { return IpAddr.V4(v4); } None { return IpAddr.V6(b); } }
            }
        }
    }
}
methods IpAddr for Display {
    display &self w:Write -> void { match self { V4(a) { a.display(w); } V6(b) { b.display(w); } } }
}
methods IpAddr for Eq<IpAddr> {
    eq &self other:IpAddr -> bool {
        match self {
            V4(a) { match other { V4(c) { return a.bits == c.bits; } V6(d) { return false; } } }
            V6(b) { match other { V4(c) { return false; } V6(d) { return b.hi == d.hi && b.lo == d.lo; } } }
        }
    }
}
methods IpAddr for Ord {
    cmp &self other:IpAddr -> int {
        match self {
            V4(a) { match other { V4(c) { return a.cmp(c); } V6(d) { return -1; } } }
            V6(b) { match other { V4(c) { return 1; } V6(d) { return b.cmp(d); } } }
        }
    }
}
methods IpAddr for Hash {
    hash &self -> u64 { match self { V4(a) { return a.hash(); } V6(b) { return combineHash(6, b.hash()); } } }
}

pub struct SocketAddrV4 { ip: Ipv4Addr, port: u16 }
pub struct SocketAddrV6 { ip: Ipv6Addr, port: u16, flowinfo: u32, scopeId: u32 }

methods SocketAddrV4 {
    parse s:str -> Result<SocketAddrV4, AddrParseError> { return parseSocketAddrV4(s); }
    of ip:Ipv4Addr port:long -> SocketAddrV4 { return SocketAddrV4 { ip: ip, port: port as u16 }; }
}
methods SocketAddrV6 {
    parse s:str -> Result<SocketAddrV6, AddrParseError> { return parseSocketAddrV6(s); }
    of ip:Ipv6Addr port:long -> SocketAddrV6 { return SocketAddrV6 { ip: ip, port: port as u16, flowinfo: 0, scopeId: 0 }; }
}

methods SocketAddrV4 for Display {
    display &self w:Write -> void { self.ip.display(w); putStr(w, ":"); putLong(w, self.port as long); }
}
methods SocketAddrV6 for Display {
    display &self w:Write -> void {
        putStr(w, "[");
        self.ip.display(w);
        if (self.scopeId != 0) { putStr(w, "%"); putLong(w, self.scopeId as long); }
        putStr(w, "]:");
        putLong(w, self.port as long);
    }
}

pub enum SocketAddr { V4(SocketAddrV4), V6(SocketAddrV6) }


methods SocketAddr {
    // Rust's SocketAddr::new.
    of ip:IpAddr port:long -> SocketAddr {
        match ip {
            V4(a) { return SocketAddr.V4(SocketAddrV4.of(a, port)); }
            V6(b) { return SocketAddr.V6(SocketAddrV6.of(b, port)); }
        }
    }
    parse s:str -> Result<SocketAddr, AddrParseError> { return parseSocketAddr(s); }
    ip &self -> IpAddr { match self { V4(a) { return IpAddr.V4(a.ip); } V6(b) { return IpAddr.V6(b.ip); } } }
    port &self -> long { match self { V4(a) { return a.port as long; } V6(b) { return b.port as long; } } }
    isIpv4 &self -> bool { match self { V4(a) { return true; } V6(b) { return false; } } }
    isIpv6 &self -> bool { return !self.isIpv4(); }
    withPort &self port:long -> SocketAddr {
        match self {
            V4(a) { return SocketAddr.V4(SocketAddrV4 { ip: a.ip, port: port as u16 }); }
            V6(b) { return SocketAddr.V6(SocketAddrV6 { ip: b.ip, port: port as u16, flowinfo: b.flowinfo, scopeId: b.scopeId }); }
        }
    }
    withIp &self ip:IpAddr -> SocketAddr { return SocketAddr.of(ip, self.port()); }
}
methods SocketAddr for Display {
    display &self w:Write -> void { match self { V4(a) { a.display(w); } V6(b) { b.display(w); } } }
}
methods SocketAddr for Eq<SocketAddr> {
    eq &self other:SocketAddr -> bool {
        match self {
            V4(a) { match other { V4(c) { return a.ip.bits == c.ip.bits && a.port == c.port; } V6(d) { return false; } } }
            V6(b) {
                match other {
                    V4(c) { return false; }
                    V6(d) { return b.ip.hi == d.ip.hi && b.ip.lo == d.ip.lo && b.port == d.port && b.flowinfo == d.flowinfo && b.scopeId == d.scopeId; }
                }
            }
        }
    }
}
methods SocketAddr for Ord {
    cmp &self other:SocketAddr -> int {
        c: int = self.ip().cmp(other.ip());
        if (c != 0) { return c; }
        return self.port().cmp(other.port());
    }
}
methods SocketAddr for Hash {
    hash &self -> u64 { return combineHash(self.ip().hash(), self.port() as u64); }
}

methods AddrParseError for Display {
    display &self w:Write -> void {
        match self {
            Ip       { putStr(w, "invalid IP address syntax"); }
            Ipv4     { putStr(w, "invalid IPv4 address syntax"); }
            Ipv6     { putStr(w, "invalid IPv6 address syntax"); }
            Socket   { putStr(w, "invalid socket address syntax"); }
            SocketV4 { putStr(w, "invalid IPv4 socket address syntax"); }
            SocketV6 { putStr(w, "invalid IPv6 socket address syntax"); }
        }
    }
}

local decimal s:str maxDigits:long max:long -> long {
    if (s.len == 0 || s.len > maxDigits) { return -1; }
    b: [u8] = s as [u8];
    if (b[0] == '0' && s.len > 1) { return -1; }
    v: long = 0;
    for c in b {
        if (!isDigit(c as long)) { return -1; }
        v = v * 10 + (c as long - '0');
    }
    if (v > max) { return -1; }
    return v;
}

local parseIpv4 s:str -> Result<Ipv4Addr, AddrParseError> {
    parts: Vec<str> = strSplit(s, '.');
    if (parts.len() != 4) { return Result.Err(AddrParseError.Ipv4); }
    bits: long = 0;
    for p in parts {
        v: long = decimal(p, 3, 255);
        if (v < 0) { return Result.Err(AddrParseError.Ipv4); }
        bits = (bits << 8) | v;
    }
    return Result.Ok(Ipv4Addr { bits: bits as u32 });
}

local hexGroups s:str inout out:[long] at:long v4Ok:bool -> long {
    if (s.len == 0) { return 0; }
    parts: Vec<str> = strSplit(s, ':');
    n: long = 0;
    for i in 0..parts.len() {
        p: str = parts.get(i);
        if (v4Ok && i == parts.len() - 1 && strContains(p, ".")) {
            r: Result<Ipv4Addr, AddrParseError> = parseIpv4(p);
            match r {
                Ok(v4) {
                    if (at + n + 2 > 8) { return -1; }
                    out[at + n] = (v4.bits as long) >> 16;
                    out[at + n + 1] = (v4.bits as long) & 0xffff;
                    n = n + 2;
                }
                Err(e) { return -1; }
            }
            continue;
        }
        if (p.len == 0 || p.len > 4 || at + n >= 8) { return -1; }
        v: long = 0;
        b: [u8] = p as [u8];
        for c in b {
            d: long = digitVal(c as long, 16);
            if (d < 0) { return -1; }
            v = v * 16 + d;
        }
        out[at + n] = v;
        n = n + 1;
    }
    return n;
}

local parseIpv6 s:str -> Result<Ipv6Addr, AddrParseError> {
    segs: [long; 8];
    gap: long = strFind(s, "::").unwrapOr(-1);
    if (gap < 0) {
        if (hexGroups(s, &segs[..], 0, true) != 8) { return Result.Err(AddrParseError.Ipv6); }
        return Result.Ok(Ipv6Addr.fromSegments(segs[..]));
    }
    head: str = s[..gap];
    tail: str = s[gap + 2..];
    if (strContains(tail, "::")) { return Result.Err(AddrParseError.Ipv6); }
    h: long = hexGroups(head, &segs[..], 0, false);
    if (h < 0) { return Result.Err(AddrParseError.Ipv6); }
    back: [long; 8];
    t: long = hexGroups(tail, &back[..], 0, true);
    if (t < 0 || h + t > 7) { return Result.Err(AddrParseError.Ipv6); }
    for k in 0..t { segs[8 - t + k] = back[k]; }
    return Result.Ok(Ipv6Addr.fromSegments(segs[..]));
}

local parseIp s:str -> Result<IpAddr, AddrParseError> {
    if (strContains(s, ":")) {
        r6: Result<Ipv6Addr, AddrParseError> = parseIpv6(s);
        match r6 { Ok(a) { return Result.Ok(IpAddr.V6(a)); } Err(e) { return Result.Err(AddrParseError.Ip); } }
    }
    r4: Result<Ipv4Addr, AddrParseError> = parseIpv4(s);
    match r4 { Ok(b) { return Result.Ok(IpAddr.V4(b)); } Err(e) { return Result.Err(AddrParseError.Ip); } }
}

local portOf s:str -> long { return decimal(s, 5, 65535); }

local parseSocketAddrV4 s:str -> Result<SocketAddrV4, AddrParseError> {
    colon: long = strFindLast(s, ":").unwrapOr(-1);
    if (colon < 0) { return Result.Err(AddrParseError.SocketV4); }
    port: long = portOf(s[colon + 1..]);
    r: Result<Ipv4Addr, AddrParseError> = parseIpv4(s[..colon]);
    match r {
        Ok(ip) { if (port >= 0) { return Result.Ok(SocketAddrV4.of(ip, port)); } }
        Err(e) {}
    }
    return Result.Err(AddrParseError.SocketV4);
}

local parseSocketAddrV6 s:str -> Result<SocketAddrV6, AddrParseError> {
    close: long = strFind(s, "]:").unwrapOr(-1);
    if (s.len < 2 || !strStartsWith(s, "[") || close < 0) { return Result.Err(AddrParseError.SocketV6); }
    port: long = portOf(s[close + 2..]);
    inner: str = s[1..close];
    scope: long = 0;
    pct: long = strFind(inner, "%").unwrapOr(-1);
    if (pct >= 0) {
        scope = decimal(inner[pct + 1..], 10, 4294967295);
        inner = inner[..pct];
    }
    r: Result<Ipv6Addr, AddrParseError> = parseIpv6(inner);
    match r {
        Ok(ip) {
            if (port >= 0 && scope >= 0) {
                a: SocketAddrV6 = SocketAddrV6.of(ip, port);
                a.scopeId = scope as u32;
                return Result.Ok(a);
            }
        }
        Err(e) {}
    }
    return Result.Err(AddrParseError.SocketV6);
}

local parseSocketAddr s:str -> Result<SocketAddr, AddrParseError> {
    if (strStartsWith(s, "[")) {
        r6: Result<SocketAddrV6, AddrParseError> = parseSocketAddrV6(s);
        match r6 { Ok(a) { return Result.Ok(SocketAddr.V6(a)); } Err(e) { return Result.Err(AddrParseError.Socket); } }
    }
    r4: Result<SocketAddrV4, AddrParseError> = parseSocketAddrV4(s);
    match r4 { Ok(b) { return Result.Ok(SocketAddr.V4(b)); } Err(e) { return Result.Err(AddrParseError.Socket); } }
}

pub trait ToSocketAddrs { toSocketAddrs &self -> Result<Vec<SocketAddr>, long>; }

local one a:SocketAddr -> Result<Vec<SocketAddr>, long> { v: Vec<SocketAddr>; v.push(a); return Result.Ok(v); }

methods SocketAddr   for ToSocketAddrs { toSocketAddrs &self -> Result<Vec<SocketAddr>, long> { return one(self); } }
methods SocketAddrV4 for ToSocketAddrs { toSocketAddrs &self -> Result<Vec<SocketAddr>, long> { return one(SocketAddr.V4(self)); } }
methods SocketAddrV6 for ToSocketAddrs { toSocketAddrs &self -> Result<Vec<SocketAddr>, long> { return one(SocketAddr.V6(self)); } }
methods str for ToSocketAddrs { toSocketAddrs &self -> Result<Vec<SocketAddr>, long> { return resolve(self); } }
methods String for ToSocketAddrs {
    toSocketAddrs &self -> Result<Vec<SocketAddr>, long> { unsafe { return resolve(self.view()); } }
}

pub lookupHost host:str -> Result<Vec<IpAddr>, long> {
    out: Vec<IpAddr>;
    lit: Result<IpAddr, AddrParseError> = parseIp(host);
    match lit { Ok(ip) { out.push(ip); return Result.Ok(out); } Err(e) {} }
    text: Result<String, long> = readFileString("/etc/hosts");
    match text {
        Ok(t) {
            all: str = "";
            unsafe { all = t.view(); }
            lines: Vec<str> = strSplit(all, '\n');
            for line in lines {
                hash: long = strFind(line, "#").unwrapOr(line.len);
                words: Vec<str> = splitBlank(line[..hash]);
                if (words.len() < 2) { continue; }
                for k in 1..words.len() {
                    if (strEq(words.get(k), host)) {
                        ip: Result<IpAddr, AddrParseError> = parseIp(words.get(0));
                        match ip { Ok(a) { out.push(a); } Err(e) {} }
                        break;
                    }
                }
            }
        }
        Err(e) {}
    }
    if (out.len() == 0 && strEq(host, "localhost")) {
        out.push(IpAddr.V4(Ipv4Addr.localhost()));
        out.push(IpAddr.V6(Ipv6Addr.localhost()));
    }
    if (out.len() == 0) { return Result.Err(Errno.NoEnt); }
    return Result.Ok(out);
}

local splitBlank s:str -> Vec<str> {
    out: Vec<str>;
    b: [u8] = s as [u8];
    i: long = 0;
    while (i < s.len) {
        while (i < s.len && (b[i] == ' ' || b[i] == '\t' || b[i] == '\r')) { i = i + 1; }
        start: long = i;
        while (i < s.len && b[i] != ' ' && b[i] != '\t' && b[i] != '\r') { i = i + 1; }
        if (i > start) { out.push(s[start..i]); }
    }
    return out;
}

local resolve s:str -> Result<Vec<SocketAddr>, long> {
    lit: Result<SocketAddr, AddrParseError> = parseSocketAddr(s);
    match lit { Ok(a) { return one(a); } Err(e) {} }
    colon: long = strFindLast(s, ":").unwrapOr(-1);
    if (colon < 0) { return Result.Err(Errno.Inval); }
    port: long = portOf(s[colon + 1..]);
    if (port < 0) { return Result.Err(Errno.Inval); }
    ips: Result<Vec<IpAddr>, long> = lookupHost(s[..colon]);
    match ips {
        Err(e) { return Result.Err(e); }
        Ok(v) {
            out: Vec<SocketAddr>;
            for x in v { out.push(SocketAddr.of(x, port)); }
            return Result.Ok(out);
        }
    }
}

local toRaw a:SocketAddr inout raw:[u8] -> long {
    match a {
        V4(v) {
            raw[0] = Family.Inet as u8;
            raw[2] = ((v.port as long) >> 8) as u8;
            raw[3] = ((v.port as long) & 255) as u8;
            for i in 0..4 { raw[4 + i] = v.ip.octet(i) as u8; }
            return 16;
        }
        V6(w) {
            raw[0] = Family.Inet6 as u8;
            raw[2] = ((w.port as long) >> 8) as u8;
            raw[3] = ((w.port as long) & 255) as u8;
            f: long = w.flowinfo as long;
            for i in 0..4 { raw[4 + i] = ((f >> (24 - 8 * i)) & 255) as u8; }
            for i in 0..16 { raw[8 + i] = w.ip.octet(i) as u8; }
            sc: long = w.scopeId as long;
            for i in 0..4 { raw[24 + i] = ((sc >> (8 * i)) & 255) as u8; }
            return SOCKADDR_MAX;
        }
    }
}

local fromRaw raw:[u8] -> Result<SocketAddr, long> {
    family: long = (raw[0] as long) | ((raw[1] as long) << 8);
    port: long = ((raw[2] as long) << 8) | (raw[3] as long);
    if (family == Family.Inet) {
        return Result.Ok(SocketAddr.V4(SocketAddrV4.of(Ipv4Addr.of(raw[4] as long, raw[5] as long, raw[6] as long, raw[7] as long), port)));
    }
    if (family == Family.Inet6) {
        hi: u64 = 0; lo: u64 = 0;
        for i in 0..8 { hi = (hi << 8) | (raw[8 + i] as u64); lo = (lo << 8) | (raw[16 + i] as u64); }
        f: long = 0; sc: long = 0;
        for i in 0..4 { f = (f << 8) | (raw[4 + i] as long); sc = sc | ((raw[24 + i] as long) << (8 * i)); }
        return Result.Ok(SocketAddr.V6(SocketAddrV6 { ip: Ipv6Addr { hi: hi, lo: lo }, port: port as u16, flowinfo: f as u32, scopeId: sc as u32 }));
    }
    return Result.Err(Errno.AfNoSupport);
}

local checked r:long -> Result<long, long> {
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(r);
}

local familyOf a:SocketAddr -> long { if (a.isIpv4()) { return Family.Inet; } return Family.Inet6; }

local openSocket a:SocketAddr kind:long -> long {
    unsafe { return syscall3(Syscall.Socket, familyOf(a), kind | SockType.CloExec, 0); }
}
local closeFd fd:long -> void { if (fd >= 0) { unsafe { syscall1(Syscall.Close, fd); } } }

local setInt fd:long level:long opt:long v:long -> Result<long, long> {
    x: int = v as int;
    unsafe { return checked(syscall6(Syscall.Setsockopt, fd, level, opt, &x as long, 4, 0)); }
}
local getInt fd:long level:long opt:long -> Result<long, long> {
    x: int = 0;
    n: int = 4;
    r: long = 0;
    unsafe { r = syscall6(Syscall.Getsockopt, fd, level, opt, &x as long, &n as long, 0); }
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(x as long);
}

struct Timeval { secs: long, usecs: long }

local setTimeout fd:long opt:long t:Option<long> -> Result<long, long> {
    tv: Timeval = Timeval { secs: 0, usecs: 0 };
    match t {
        Some(ns) {
            if (ns <= 0) { return Result.Err(Errno.Inval); }
            tv.secs = ns / NS_PER_SECOND;
            tv.usecs = (ns % NS_PER_SECOND) / 1000;
            if (tv.secs == 0 && tv.usecs == 0) { tv.usecs = 1; }
        }
        None {}
    }
    unsafe { return checked(syscall6(Syscall.Setsockopt, fd, Level.Socket, opt, &tv as long, 16, 0)); }
}
local getTimeout fd:long opt:long -> Result<Option<long>, long> {
    tv: Timeval = Timeval { secs: 0, usecs: 0 };
    n: int = 16;
    r: long = 0;
    unsafe { r = syscall6(Syscall.Getsockopt, fd, Level.Socket, opt, &tv as long, &n as long, 0); }
    if (r < 0) { return Result.Err(-r); }
    if (tv.secs == 0 && tv.usecs == 0) { return Result.Ok(Option.None); }
    return Result.Ok(Option.Some(tv.secs * NS_PER_SECOND + tv.usecs * 1000));
}

local setNonblock fd:long on:bool -> Result<long, long> {
    v: int = 0;
    if (on) { v = 1; }
    unsafe { return checked(syscall3(Syscall.Ioctl, fd, FIONBIO, &v as long)); }
}

local nameOf fd:long peer:bool -> Result<SocketAddr, long> {
    raw: [u8; 28];
    n: int = 28;
    r: long = 0;
    nr: Syscall = Syscall.Getsockname;
    if (peer) { nr = Syscall.Getpeername; }
    unsafe { r = syscall3(nr, fd, &raw as long, &n as long); }
    if (r < 0) { return Result.Err(-r); }
    return fromRaw(raw[..]);
}

local dupFd fd:long -> Result<long, long> {
    unsafe { return checked(syscall3(Syscall.Fcntl, fd, F_DUPFD_CLOEXEC, 0)); }
}

local takeErr fd:long -> Result<Option<long>, long> {
    r: Result<long, long> = getInt(fd, Level.Socket, SockOpt.Error);
    match r {
        Ok(e) { if (e == 0) { return Result.Ok(Option.None); } return Result.Ok(Option.Some(e)); }
        Err(x) { return Result.Err(x); }
    }
}

local ttlLevel fd:long -> long {
    a: Result<SocketAddr, long> = nameOf(fd, false);
    match a { Ok(s) { if (s.isIpv6()) { return Level.Ipv6; } } Err(e) {} }
    return Level.Ip;
}
local ttlOpt level:long -> long { if (level == Level.Ipv6) { return ProtoOpt.Ipv6Hops; } return ProtoOpt.IpTtl; }

local recvRaw fd:long ptr:long len:long flags:long -> long {
    loop {
        n: long = 0;
        unsafe { n = syscall6(Syscall.Recvfrom, fd, ptr, len, flags, 0, 0); }
        if (n != -Errno.Intr) { return n; }
    }
    return 0;
}
local sendRaw fd:long ptr:long len:long -> long {
    loop {
        n: long = 0;
        unsafe { n = syscall6(Syscall.Sendto, fd, ptr, len, MsgFlag.NoSignal, 0, 0); }
        if (n != -Errno.Intr) { return n; }
    }
    return 0;
}
local sendAll fd:long ptr:long len:long -> long {
    off: long = 0;
    while (off < len) {
        n: long = sendRaw(fd, ptr + off, len - off);
        if (n < 0) { if (off > 0) { return off; } return n; }
        if (n == 0) { return off; }
        off = off + n;
    }
    return off;
}

pub enum Shutdown: long { Read = 0, Write = 1, Both = 2 }

pub struct TcpStream { fd: int }

methods TcpStream for Default { new -> TcpStream { return TcpStream { fd: -1 }; } }
methods TcpStream for Drop    { drop &self -> void { self.close(); } }

methods TcpStream for Read {
    read &self ptr:long len:long -> long { return recvRaw(self.fd, ptr, len, 0); }
}
methods TcpStream for Write {
    write &self ptr:long len:long -> long { return sendAll(self.fd, ptr, len); }
}

local connectOne a:SocketAddr timeoutNs:long -> Result<TcpStream, long> {
    fd: long = openSocket(a, SockType.Stream);
    if (fd < 0) { return Result.Err(-fd); }
    s: TcpStream = TcpStream { fd: fd as int };
    raw: [u8; 28];
    len: long = toRaw(a, &raw[..]);
    if (timeoutNs > 0) {
        nb: Result<long, long> = setNonblock(fd, true);
        if (nb.isErr()) { return Result.Err(nb.unwrapErr()); }
    }
    r: long = 0;
    unsafe { r = syscall3(Syscall.Connect, fd, &raw as long, len); }
    if (r == -Errno.InProgress && timeoutNs > 0) {
        pfd: [u8; 8];
        for i in 0..4 { pfd[i] = ((fd >> (8 * i)) & 255) as u8; }
        pfd[4] = POLLOUT as u8;
        ms: long = (timeoutNs + 999999) / 1000000;
        loop {
            unsafe { r = syscall3(Syscall.Poll, &pfd as long, 1, ms); }
            if (r != -Errno.Intr) { break; }
        }
        if (r == 0) { return Result.Err(Errno.TimedOut); }
        if (r > 0) {
            pending: Result<Option<long>, long> = takeErr(fd);
            match pending {
                Ok(e) { r = -(e.unwrapOr(0)); }
                Err(x) { r = -x; }
            }
        }
    }
    if (r < 0) { return Result.Err(-r); }
    if (timeoutNs > 0) {
        nb: Result<long, long> = setNonblock(fd, false);
        if (nb.isErr()) { return Result.Err(nb.unwrapErr()); }
    }
    return Result.Ok(s);
}

local connectAny addrs:Result<Vec<SocketAddr>, long> -> Result<TcpStream, long> {
    match addrs {
        Err(e) { return Result.Err(e); }
        Ok(v) {
            last: long = Errno.Inval;
            for a in v {
                r: Result<TcpStream, long> = connectOne(a, 0);
                match r { Ok(s) { return Result.Ok(s); } Err(e) { last = e; } }
            }
            return Result.Err(last);
        }
    }
}

methods TcpStream {
    connect<A: ToSocketAddrs> addr:A -> Result<TcpStream, long> { return connectAny(addr.toSocketAddrs()); }
    connectTimeout a:SocketAddr ns:long -> Result<TcpStream, long> {
        if (ns <= 0) { return Result.Err(Errno.Inval); }
        return connectOne(a, ns);
    }

    peerAddr  &self -> Result<SocketAddr, long> { return nameOf(self.fd, true); }
    localAddr &self -> Result<SocketAddr, long> { return nameOf(self.fd, false); }

    shutdown &self how:Shutdown -> Result<long, long> {
        unsafe { return checked(syscall2(Syscall.Shutdown, self.fd, how)); }
    }

    readSome &self inout buf:[u8] -> long { unsafe { return recvRaw(self.fd, buf.ptr, buf.len, 0); } }
    readExact &self inout buf:[u8] -> Result<long, long> {
        got: long = 0;
        while (got < buf.len) {
            n: long = 0;
            unsafe { n = recvRaw(self.fd, buf.ptr + got, buf.len - got, 0); }
            if (n < 0) { return Result.Err(-n); }
            if (n == 0) { return Result.Err(0); }
            got = got + n;
        }
        return Result.Ok(got);
    }
    readToString &self -> Result<String, long> {
        out: String;
        chunk: [u8; 4096];
        loop {
            n: long = 0;
            unsafe { n = recvRaw(self.fd, &chunk as long, 4096, 0); }
            if (n < 0) { return Result.Err(-n); }
            if (n == 0) { break; }
            out.pushStr(chunk[..n] as str);
        }
        return Result.Ok(out);
    }
    peek &self inout buf:[u8] -> long { unsafe { return recvRaw(self.fd, buf.ptr, buf.len, MsgFlag.Peek); } }

    writeStr   &self s:str  -> long { unsafe { return sendAll(self.fd, s.ptr, s.len); } }
    writeBytes &self b:[u8] -> long { unsafe { return sendAll(self.fd, b.ptr, b.len); } }
    flush &self -> long { return 0; }

    setReadTimeout  &self t:Option<long> -> Result<long, long> { return setTimeout(self.fd, SockOpt.RecvTimeout, t); }
    setWriteTimeout &self t:Option<long> -> Result<long, long> { return setTimeout(self.fd, SockOpt.SendTimeout, t); }
    readTimeout  &self -> Result<Option<long>, long> { return getTimeout(self.fd, SockOpt.RecvTimeout); }
    writeTimeout &self -> Result<Option<long>, long> { return getTimeout(self.fd, SockOpt.SendTimeout); }

    setNodelay &self on:bool -> Result<long, long> { v: long = 0; if (on) { v = 1; } return setInt(self.fd, Level.Tcp, ProtoOpt.TcpNoDelay, v); }
    nodelay    &self -> Result<bool, long> {
        r: Result<long, long> = getInt(self.fd, Level.Tcp, ProtoOpt.TcpNoDelay);
        match r { Ok(v) { return Result.Ok(v != 0); } Err(e) { return Result.Err(e); } }
    }
    setTtl &self ttl:long -> Result<long, long> { lv: long = ttlLevel(self.fd); return setInt(self.fd, lv, ttlOpt(lv), ttl); }
    ttl    &self -> Result<long, long> { lv: long = ttlLevel(self.fd); return getInt(self.fd, lv, ttlOpt(lv)); }

    setNonblocking &self on:bool -> Result<long, long> { return setNonblock(self.fd, on); }
    tryClone &self -> Result<TcpStream, long> {
        r: Result<long, long> = dupFd(self.fd);
        match r { Ok(fd) { return Result.Ok(TcpStream { fd: fd as int }); } Err(e) { return Result.Err(e); } }
    }
    takeError &self -> Result<Option<long>, long> { return takeErr(self.fd); }

    rawFd &self -> long { return self.fd as long; }
    intoRawFd self -> long { fd: long = self.fd as long; self.fd = -1; return fd; }
    unsafe fromRawFd fd:long -> TcpStream { return TcpStream { fd: fd as int }; }
    isOpen &self -> bool { return self.fd >= 0; }
    close &self -> void { closeFd(self.fd); self.fd = -1; }
}

// A connected Unix-domain stream socket: a peer on this machine named by a path, such as an X
// server's /tmp/.X11-unix/X0.
pub struct UnixStream { fd: int }

methods UnixStream for Default { new -> UnixStream { return UnixStream { fd: -1 }; } }
methods UnixStream for Drop  { drop &self -> void { self.close(); } }
methods UnixStream for Read  { read &self ptr:long len:long -> long { return recvRaw(self.fd, ptr, len, 0); } }
methods UnixStream for Write { write &self ptr:long len:long -> long { return sendAll(self.fd, ptr, len); } }

methods UnixStream {
    connect path:str -> Result<UnixStream, long> {
        if (path.len >= 108) { return Result.Err(Errno.NameTooLong); }
        fd: long = 0;
        unsafe { fd = syscall3(Syscall.Socket, 1, SockType.Stream | SockType.CloExec, 0); }   // AF_UNIX
        if (fd < 0) { return Result.Err(-fd); }
        s: UnixStream = UnixStream { fd: fd as int };
        // sockaddr_un: the family, then the path, NUL-terminated
        raw: [u8; 110];
        raw[0] = 1;
        raw[1] = 0;
        p: [u8] = path as [u8];
        for i in 0..p.len { raw[2 + i] = p[i]; }
        raw[2 + p.len] = 0;
        r: long = 0;
        unsafe { r = syscall3(Syscall.Connect, fd, &raw as long, 3 + p.len); }
        if (r < 0) { return Result.Err(-r); }
        return Result.Ok(s);
    }
    readSome &self inout buf:[u8] -> long { unsafe { return recvRaw(self.fd, buf.ptr, buf.len, 0); } }
    readExact &self inout buf:[u8] -> Result<long, long> {
        got: long = 0;
        while (got < buf.len) {
            n: long = 0;
            unsafe { n = recvRaw(self.fd, buf.ptr + got, buf.len - got, 0); }
            if (n < 0) { return Result.Err(-n); }
            if (n == 0) { return Result.Err(0); }
            got = got + n;
        }
        return Result.Ok(got);
    }
    writeBytes &self b:[u8] -> long { unsafe { return sendAll(self.fd, b.ptr, b.len); } }
    writeStr   &self s:str  -> long { unsafe { return sendAll(self.fd, s.ptr, s.len); } }
    setNonblocking &self on:bool -> Result<long, long> { return setNonblock(self.fd, on); }
    rawFd &self -> long { return self.fd as long; }
    isOpen &self -> bool { return self.fd >= 0; }
    close &self -> void { closeFd(self.fd); self.fd = -1; }
}

pub struct TcpListener { fd: int }
pub struct Incoming { fd: int }

methods TcpListener for Default { new -> TcpListener { return TcpListener { fd: -1 }; } }
methods TcpListener for Drop    { drop &self -> void { self.close(); } }

local listenOne a:SocketAddr backlog:long -> Result<TcpListener, long> {
    fd: long = openSocket(a, SockType.Stream);
    if (fd < 0) { return Result.Err(-fd); }
    l: TcpListener = TcpListener { fd: fd as int };
    reuse: Result<long, long> = setInt(fd, Level.Socket, SockOpt.ReuseAddr, 1);
    raw: [u8; 28];
    len: long = toRaw(a, &raw[..]);
    r: long = 0;
    unsafe { r = syscall3(Syscall.Bind, fd, &raw as long, len); }
    if (r == 0) { unsafe { r = syscall2(Syscall.Listen, fd, backlog); } }
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(l);
}
local listenAny addrs:Result<Vec<SocketAddr>, long> backlog:long -> Result<TcpListener, long> {
    match addrs {
        Err(e) { return Result.Err(e); }
        Ok(v) {
            last: long = Errno.Inval;
            for a in v {
                r: Result<TcpListener, long> = listenOne(a, backlog);
                match r { Ok(l) { return Result.Ok(l); } Err(e) { last = e; } }
            }
            return Result.Err(last);
        }
    }
}

methods TcpListener {
    bind<A: ToSocketAddrs> addr:A -> Result<TcpListener, long> { return listenAny(addr.toSocketAddrs(), DEFAULT_BACKLOG); }
    // How many connections may wait to be accepted (capped at somaxconn); Rust fixes it at 128.
    bindWithBacklog<A: ToSocketAddrs> addr:A backlog:long -> Result<TcpListener, long> { return listenAny(addr.toSocketAddrs(), backlog); }

    // The next connection and where it came from.
    accept &self -> Result<(TcpStream, SocketAddr), long> {
        raw: [u8; 28];
        n: int = 28;
        loop {
            c: long = 0;
            unsafe { c = syscall4(Syscall.Accept4, self.fd, &raw as long, &n as long, SockType.CloExec); }
            if (c >= 0) {
                s: TcpStream = TcpStream { fd: c as int };
                a: Result<SocketAddr, long> = fromRaw(raw[..]);
                match a { Ok(from) { return Result.Ok((s, from)); } Err(e) { return Result.Err(e); } }
            }
            if (c != -Errno.Intr) { return Result.Err(-c); }
        }
        return Result.Err(Errno.Inval);
    }
    incoming &self -> Incoming { return Incoming { fd: self.fd }; }

    localAddr &self -> Result<SocketAddr, long> { return nameOf(self.fd, false); }
    setTtl &self ttl:long -> Result<long, long> { lv: long = ttlLevel(self.fd); return setInt(self.fd, lv, ttlOpt(lv), ttl); }
    ttl    &self -> Result<long, long> { lv: long = ttlLevel(self.fd); return getInt(self.fd, lv, ttlOpt(lv)); }
    setNonblocking &self on:bool -> Result<long, long> { return setNonblock(self.fd, on); }
    tryClone &self -> Result<TcpListener, long> {
        r: Result<long, long> = dupFd(self.fd);
        match r { Ok(fd) { return Result.Ok(TcpListener { fd: fd as int }); } Err(e) { return Result.Err(e); } }
    }
    takeError &self -> Result<Option<long>, long> { return takeErr(self.fd); }
    rawFd &self -> long { return self.fd as long; }
    intoRawFd self -> long { fd: long = self.fd as long; self.fd = -1; return fd; }
    unsafe fromRawFd fd:long -> TcpListener { return TcpListener { fd: fd as int }; }
    close &self -> void { closeFd(self.fd); self.fd = -1; }
}

methods Incoming for Iter<Result<TcpStream, long>> {
    hasNext &self -> bool { return true; }
    next &self -> Result<TcpStream, long> {
        l: TcpListener = TcpListener { fd: self.fd };
        r: Result<(TcpStream, SocketAddr), long> = l.accept();
        l.fd = -1;                       // borrowed the listener's fd: not ours to close
        match r { Ok(p) { s, a = p; return Result.Ok(s); } Err(e) { return Result.Err(e); } }
    }
}

pub struct UdpSocket { fd: int }

methods UdpSocket for Default { new -> UdpSocket { return UdpSocket { fd: -1 }; } }
methods UdpSocket for Drop    { drop &self -> void { self.close(); } }

local udpOne a:SocketAddr -> Result<UdpSocket, long> {
    fd: long = openSocket(a, SockType.Dgram);
    if (fd < 0) { return Result.Err(-fd); }
    u: UdpSocket = UdpSocket { fd: fd as int };
    raw: [u8; 28];
    len: long = toRaw(a, &raw[..]);
    r: long = 0;
    unsafe { r = syscall3(Syscall.Bind, fd, &raw as long, len); }
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(u);
}

local recvFromRaw fd:long inout buf:[u8] flags:long -> Result<(long, SocketAddr), long> {
    raw: [u8; 28];
    n: int = 28;
    r: long = 0;
    loop {
        unsafe { r = syscall6(Syscall.Recvfrom, fd, buf.ptr, buf.len, flags, &raw as long, &n as long); }
        if (r != -Errno.Intr) { break; }
    }
    if (r < 0) { return Result.Err(-r); }
    a: Result<SocketAddr, long> = fromRaw(raw[..]);
    match a {
        Ok(from) { return Result.Ok((r, from)); }
        Err(e) { return Result.Err(e); }
    }
}

methods UdpSocket {
    bind<A: ToSocketAddrs> addr:A -> Result<UdpSocket, long> {
        all: Result<Vec<SocketAddr>, long> = addr.toSocketAddrs();
        match all {
            Err(e) { return Result.Err(e); }
            Ok(v) {
                last: long = Errno.Inval;
                for a in v {
                    r: Result<UdpSocket, long> = udpOne(a);
                    match r { Ok(u) { return Result.Ok(u); } Err(e) { last = e; } }
                }
                return Result.Err(last);
            }
        }
    }

    recvFrom &self inout buf:[u8] -> Result<(long, SocketAddr), long> { return recvFromRaw(self.fd, buf, 0); }
    peekFrom &self inout buf:[u8] -> Result<(long, SocketAddr), long> { return recvFromRaw(self.fd, buf, MsgFlag.Peek); }

    // To the first address `addr` names, as Rust does.
    sendTo<A: ToSocketAddrs> &self buf:[u8] addr:A -> Result<long, long> {
        all: Result<Vec<SocketAddr>, long> = addr.toSocketAddrs();
        match all {
            Err(e) { return Result.Err(e); }
            Ok(v) {
                if (v.len() == 0) { return Result.Err(Errno.Inval); }
                raw: [u8; 28];
                len: long = toRaw(v.get(0), &raw[..]);
                r: long = 0;
                loop {
                    unsafe { r = syscall6(Syscall.Sendto, self.fd, buf.ptr, buf.len, MsgFlag.NoSignal, &raw as long, len); }
                    if (r != -Errno.Intr) { break; }
                }
                return checked(r);
            }
        }
    }
    connect<A: ToSocketAddrs> &self addr:A -> Result<long, long> {
        all: Result<Vec<SocketAddr>, long> = addr.toSocketAddrs();
        match all {
            Err(e) { return Result.Err(e); }
            Ok(v) {
                last: long = Errno.Inval;
                for a in v {
                    raw: [u8; 28];
                    len: long = toRaw(a, &raw[..]);
                    r: long = 0;
                    unsafe { r = syscall3(Syscall.Connect, self.fd, &raw as long, len); }
                    if (r == 0) { return Result.Ok(0); }
                    last = -r;
                }
                return Result.Err(last);
            }
        }
    }
    send &self buf:[u8] -> Result<long, long> { unsafe { return checked(sendRaw(self.fd, buf.ptr, buf.len)); } }
    recv &self inout buf:[u8] -> Result<long, long> { unsafe { return checked(recvRaw(self.fd, buf.ptr, buf.len, 0)); } }
    peek &self inout buf:[u8] -> Result<long, long> { unsafe { return checked(recvRaw(self.fd, buf.ptr, buf.len, MsgFlag.Peek)); } }

    localAddr &self -> Result<SocketAddr, long> { return nameOf(self.fd, false); }
    peerAddr  &self -> Result<SocketAddr, long> { return nameOf(self.fd, true); }

    setBroadcast &self on:bool -> Result<long, long> { v: long = 0; if (on) { v = 1; } return setInt(self.fd, Level.Socket, SockOpt.Broadcast, v); }
    broadcast    &self -> Result<bool, long> {
        r: Result<long, long> = getInt(self.fd, Level.Socket, SockOpt.Broadcast);
        match r { Ok(v) { return Result.Ok(v != 0); } Err(e) { return Result.Err(e); } }
    }
    setTtl &self ttl:long -> Result<long, long> { lv: long = ttlLevel(self.fd); return setInt(self.fd, lv, ttlOpt(lv), ttl); }
    ttl    &self -> Result<long, long> { lv: long = ttlLevel(self.fd); return getInt(self.fd, lv, ttlOpt(lv)); }
    setReadTimeout  &self t:Option<long> -> Result<long, long> { return setTimeout(self.fd, SockOpt.RecvTimeout, t); }
    setWriteTimeout &self t:Option<long> -> Result<long, long> { return setTimeout(self.fd, SockOpt.SendTimeout, t); }
    readTimeout  &self -> Result<Option<long>, long> { return getTimeout(self.fd, SockOpt.RecvTimeout); }
    writeTimeout &self -> Result<Option<long>, long> { return getTimeout(self.fd, SockOpt.SendTimeout); }
    setNonblocking &self on:bool -> Result<long, long> { return setNonblock(self.fd, on); }
    tryClone &self -> Result<UdpSocket, long> {
        r: Result<long, long> = dupFd(self.fd);
        match r { Ok(fd) { return Result.Ok(UdpSocket { fd: fd as int }); } Err(e) { return Result.Err(e); } }
    }
    takeError &self -> Result<Option<long>, long> { return takeErr(self.fd); }
    rawFd &self -> long { return self.fd as long; }
    intoRawFd self -> long { fd: long = self.fd as long; self.fd = -1; return fd; }
    unsafe fromRawFd fd:long -> UdpSocket { return UdpSocket { fd: fd as int }; }
    close &self -> void { closeFd(self.fd); self.fd = -1; }
}
