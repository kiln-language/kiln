// A file-private `twice`, which only this file's functions may call.
local twice x:long -> long { return x * 20; }
pub viaA x:long -> long { return twice(x); }
