// Readiness polling over epoll, after mio's Poll: wait until any of many descriptors can be read
// or written, then handle just those. A descriptor is its own token: an Event names its fd.
//
//     p: Poller = Poller.open().unwrap();
//     p.add(listener.rawFd(), Interest.Readable).unwrap();
//     ready: Vec<Event>;
//     loop {
//         p.wait(&ready, Option.None).unwrap();
//         for ev in ready { if (ev.readable()) { ... ev.fd ... } }
//     }
//
// Level-triggered: a descriptor stays ready until it has been read or written to exhaustion.
#include <{core, sys, option, result, vec}>

pub enum Interest: long { Readable = 0x2001, Writable = 0x2004, Both = 0x2005 }   // RDHUP always on

local IN: long = 1;
local OUT: long = 4;
local ERR: long = 8;
local HUP: long = 16;
local RDHUP: long = 0x2000;
local EXCLUSIVE: long = 0x10000000;
local CLOEXEC: long = 0x80000;
local CTL_ADD: long = 1;
local CTL_DEL: long = 2;
local CTL_MOD: long = 3;
local EVENT_SIZE: long = 12;             // struct epoll_event is packed: u32 events, u64 data
local CAPACITY: long = 256;              // events taken per wait

pub struct Event { fd: long, bits: long }

methods Event {
    readable &self -> bool { return (self.bits & IN) != 0; }
    writable &self -> bool { return (self.bits & OUT) != 0; }
    // The peer closed its side (or both): reads will drain what is left, then see the end.
    hangup   &self -> bool { return (self.bits & (HUP | RDHUP)) != 0; }
    error    &self -> bool { return (self.bits & ERR) != 0; }
}

pub struct Poller { ep: int, buf: Vec<u8> }

methods Poller for Drop {
    drop &self -> void { if (self.ep >= 0) { unsafe { syscall1(Syscall.Close, self.ep); } self.ep = -1; } }
}

local ctl ep:long op:long fd:long events:long -> Result<long, long> {
    ev: [u8; 12];
    for k in 0..4 { ev[k] = ((events >> (8 * k)) & 255) as u8; }
    for k in 0..8 { ev[4 + k] = ((fd >> (8 * k)) & 255) as u8; }
    r: long = 0;
    unsafe { r = syscall4(Syscall.EpollCtl, ep, op, fd, &ev as long); }
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(0);
}

methods Poller {
    open -> Result<Poller, long> {
        ep: long = 0;
        unsafe { ep = syscall1(Syscall.EpollCreate1, CLOEXEC); }
        if (ep < 0) { return Result.Err(-ep); }
        b: Vec<u8>;
        for i in 0..CAPACITY * EVENT_SIZE { b.push(0); }
        return Result.Ok(Poller { ep: ep as int, buf: b });
    }

    add    &self fd:long interest:Interest -> Result<long, long> { return ctl(self.ep, CTL_ADD, fd, interest as long); }
    modify &self fd:long interest:Interest -> Result<long, long> { return ctl(self.ep, CTL_MOD, fd, interest as long); }
    remove &self fd:long -> Result<long, long> { return ctl(self.ep, CTL_DEL, fd, 0); }
    // For a descriptor several pollers watch (one listener, a poller per thread): an event wakes
    // one of them rather than all. The kernel refuses RDHUP alongside it, so it is left out.
    addExclusive &self fd:long interest:Interest -> Result<long, long> {
        return ctl(self.ep, CTL_ADD, fd, ((interest as long) & ~RDHUP) | EXCLUSIVE);
    }

    // Wait until something is ready, or `timeout` nanoseconds pass (None: no limit). `ready` is
    // cleared and refilled; the count, which is 0 on a timeout or a signal.
    wait &self inout ready:Vec<Event> timeout:Option<long> -> Result<long, long> {
        ready.clear();
        ms: long = -1;
        match timeout { Some(ns) { ms = (ns + 999999) / 1000000; } None {} }
        n: long = 0;
        unsafe { n = syscall4(Syscall.EpollWait, self.ep, self.buf.buf.ptr as long, CAPACITY, ms); }
        if (n == -Errno.Intr) { return Result.Ok(0); }
        if (n < 0) { return Result.Err(-n); }
        for i in 0..n {
            at: long = i * EVENT_SIZE;
            bits: long = 0;
            fd: long = 0;
            for k in 0..4 { bits = bits | ((self.buf.get(at + k) as long) << (8 * k)); }
            for k in 0..8 { fd = fd | ((self.buf.get(at + 4 + k) as long) << (8 * k)); }
            ready.push(Event { fd: fd, bits: bits });
        }
        return Result.Ok(n);
    }

    rawFd &self -> long { return self.ep as long; }
}
