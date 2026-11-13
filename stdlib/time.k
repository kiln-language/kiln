// Reading the clock.
//
// Two clocks matter most, because they answer different questions and are wrong for each
// other's. The MONOTONIC one counts from an arbitrary point (boot) and never moves backwards, so
// it is the one to measure durations with. The REALTIME one counts from the Unix epoch and can
// be set or stepped by NTP — two readings can come back in the wrong order — so it is the one
// for saying WHEN something happened, not how long it took. `clockNow` reads any of the others
// the kernel keeps: CPU time used by the process or by this thread, or a monotonic clock that
// also counts time spent suspended.
//
//     start: Instant = monotonic();
//     work();
//     println("{} us", elapsedUs(start));
#include <{core, sys, cmp}>

// The clocks clock_gettime(2) can read. A backed enum: each variant is the kernel's clock id.
pub enum Clock: long {
    Realtime = 0,
    Monotonic = 1,
    ProcessCpu = 2,     // CPU time consumed by every thread of this process
    ThreadCpu = 3,      // CPU time consumed by the calling thread
    MonotonicRaw = 4,   // monotonic, without NTP's rate adjustment
    Boottime = 7        // monotonic, counting time the machine spent suspended
}

local NS_PER_SEC: long = 1000000000;
local NS_PER_MS:  long = 1000000;
local NS_PER_US:  long = 1000;

// A point in time: whole seconds, plus nanoseconds within that second — the shape the kernel
// reports. Two fields rather than one nanosecond count because a wall-clock value in
// nanoseconds overflows a signed long in 2262, and a timestamp that stops working is not a
// timestamp. Durations, which are differences, are plain nanosecond longs and have no such
// problem: a long holds 292 years of them.
pub struct Instant { secs: long, nanos: long }

methods Instant {
    // Since this Instant's own epoch. Safe for a monotonic reading (counted from boot);
    // for a realtime one, prefer asSecs and the fraction separately past the year 2262.
    asNanos  &self -> long { return self.secs * NS_PER_SEC + self.nanos; }
    asMicros &self -> long { return self.secs * (NS_PER_SEC / NS_PER_US) + self.nanos / NS_PER_US; }
    asMillis &self -> long { return self.secs * (NS_PER_SEC / NS_PER_MS) + self.nanos / NS_PER_MS; }
    asSecs   &self -> long { return self.secs; }

    // Nanoseconds from `earlier` to this. Computed field-wise rather than by subtracting two
    // asNanos values, so a realtime pair far past 2262 still gives the right difference.
    since &self earlier:Instant -> long {
        return (self.secs - earlier.secs) * NS_PER_SEC + (self.nanos - earlier.nanos);
    }

    // This instant moved by `ns` nanoseconds (either sign), kept in canonical form: the
    // nanosecond field stays in 0..1e9.
    plusNanos &self ns:long -> Instant {
        s: long = self.secs + ns / NS_PER_SEC;
        n: long = self.nanos + ns % NS_PER_SEC;
        if (n >= NS_PER_SEC) { s = s + 1; n = n - NS_PER_SEC; }
        if (n < 0) { s = s - 1; n = n + NS_PER_SEC; }
        return Instant { secs: s, nanos: n };
    }
}

// Earlier sorts first. Only meaningful between two readings of the same clock.
methods Instant for Ord {
    cmp &self other:Instant -> int {
        if (self.secs != other.secs) { return self.secs.cmp(other.secs); }
        return self.nanos.cmp(other.nanos);
    }
}

// The time on any clock.
pub clockNow c:Clock -> Instant {
    ts: Timespec = Timespec { secs: 0, nanos: 0 };
    unsafe { syscall2(Syscall.ClockGettime, c as long, &ts as long); }
    return Instant { secs: ts.secs, nanos: ts.nanos };
}

// Never moves backwards. Measure WITH this one.
pub monotonic -> Instant { return clockNow(Clock.Monotonic); }

// Since the Unix epoch, and settable. Say WHEN with this one.
pub now -> Instant { return clockNow(Clock.Realtime); }

// Nanoseconds since `start` on the monotonic clock — the whole of most timing code.
pub elapsedNs start:Instant -> long { return monotonic().since(start); }
pub elapsedUs start:Instant -> long { return elapsedNs(start) / NS_PER_US; }
pub elapsedMs start:Instant -> long { return elapsedNs(start) / NS_PER_MS; }

// Suspend for `ns` nanoseconds. Returns 0, or -EINTR if a signal cut it short — in which case
// it really did return early. `sleepFor` is the form that finishes the sleep regardless.
pub sleepNanos ns:long -> long {
    req: Timespec = timespecOf(ns);
    unsafe { return syscall2(Syscall.Nanosleep, &req as long, 0); }
}

// Suspend for the whole of `ns` nanoseconds: an interrupted sleep resumes for what was left.
pub sleepFor ns:long -> void { sysSleep(ns); }
