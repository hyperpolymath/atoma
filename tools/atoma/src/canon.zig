// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Atoma — canonical form of the Core Spec IR (`.cspec`, wire format v1).
//
// This module is the *untrusted* reference canonicaliser. The trusted encoder is
// `encode : Contract -> String` in `examples/atoma/frame-v1/abi/FrameAbi.idr`
// (Face A); the two are tied together by the golden-corpus test in `canon.zig`
// and by the seam gate. The eight rules it implements are
// docs/spec/ATOMA-SPEC.adoc §2.4. Nothing in this file is in the TCB: it may be
// replaced, rewritten or thrown away without changing what Atoma proves.
//
// Equality of canonical byte strings is the Atoma notion of "Face A and Face
// B say the same thing". It is a *syntactic* agreement check, not a proof of
// semantic equivalence (§2.5 of the spec).
//
// Canonicalisation rules (normative; mirrored by `encode` in CoreSpec.idr):
//   R1  Comments (`#` to end of line) and blank lines are dropped.
//   R2  A line is reduced to tokens: `(` and `)` are one-character tokens, every
//       other token is a maximal run of non-space characters.
//   R3  Tokens are separated by exactly one space, each line ends with exactly
//       one `\n`, ASCII only, no tabs, no trailing whitespace.
//   R4  Under `forall`/`exists`, binder names are renamed to `%0`, `%1`, ... in
//       order of occurrence (alpha-normalisation). Free names are untouched.
//       v1 restriction: a binder type must be atomic (a named sort). Compound
//       binder types must be introduced through a `sort` declaration first.
//   R5  Integer literals are normalised to unsigned decimal with no leading
//       zeros (`0x10` -> `16`, `1_000` -> `1000`, `0b1010` -> `10`).
//   R6  *Set-valued* lines are sorted: `cap`, `assigns`, `field`, `sort`.
//       `field` sorts by (struct, numeric offset); the others lexicographically.
//   R7  *Positional* lines keep their order because position is ABI-significant:
//       `cspec`, `contract`, `kind`, `param`, `borrow`, `requires`, `ensures`,
//       `invariant`, `assert`, `layout`, `bound`. Sorting them would hide an
//       ABI-order disagreement between the Idris2 face and the Zig face, which
//       is exactly the bug we want to see.
//   R8  Domains are separated so that a digest of one artifact class can never
//       be read as a digest of another:
//           "atoma.cspec.v1\n" ++ canonical bytes   contract specification
//           "atoma.vc.v1\n"    ++ raw bytes         SMT-LIB verification condition
//           "atoma.dk.v1\n"    ++ raw bytes         Dedukti witness
//           "atoma.src.v1\n"   ++ raw bytes         proof source (Agda module)

const std = @import("std");
const Allocator = std.mem.Allocator;

pub const domain_spec = "atoma.cspec.v1\n";
pub const domain_dk = "atoma.dk.v1\n";
pub const domain_vc = "atoma.vc.v1\n";
pub const domain_src = "atoma.src.v1\n";

/// Set-valued lines: sorted in canonical form (R6).
const set_valued = [_][]const u8{ "cap", "assigns", "field", "sort" };

pub const Error = error{
    OutOfMemory,
    MalformedBinder,
    UnbalancedParens,
    BadInteger,
};

pub const Canon = struct {
    bytes: []u8,
    /// BLAKE3 of domain_spec ++ bytes.
    digest: [32]u8,

    pub fn deinit(self: Canon, alloc: Allocator) void {
        alloc.free(self.bytes);
    }

    pub fn hex(self: Canon) [64]u8 {
        return toHex(self.digest);
    }
};

pub fn toHex(d: [32]u8) [64]u8 {
    const alphabet = "0123456789abcdef";
    var out: [64]u8 = undefined;
    for (d, 0..) |b, i| {
        out[2 * i] = alphabet[b >> 4];
        out[2 * i + 1] = alphabet[b & 0xf];
    }
    return out;
}

pub fn digestOf(domain: []const u8, bytes: []const u8) [32]u8 {
    var h = std.crypto.hash.Blake3.init(.{});
    h.update(domain);
    h.update(bytes);
    var out: [32]u8 = undefined;
    h.final(&out);
    return out;
}

pub fn digestHex(domain: []const u8, bytes: []const u8) [64]u8 {
    return toHex(digestOf(domain, bytes));
}

// ─────────────────────────────────────────────────────────────────────────────
// Tokenisation (R2, R3)
// ─────────────────────────────────────────────────────────────────────────────

/// Split one line into tokens, treating `(` and `)` as single-character tokens.
/// `out` is cleared first; tokens alias the input slice.
pub fn tokenise(alloc: Allocator, line: []const u8, out: *std.ArrayListUnmanaged([]const u8)) !void {
    out.clearRetainingCapacity();
    var i: usize = 0;
    while (i < line.len) {
        const c = line[i];
        if (c == ' ' or c == '\t' or c == '\r') {
            i += 1;
            continue;
        }
        if (c == '(' or c == ')') {
            try out.append(alloc, line[i .. i + 1]);
            i += 1;
            continue;
        }
        const start = i;
        while (i < line.len and line[i] != ' ' and line[i] != '\t' and line[i] != '\r' and
            line[i] != '(' and line[i] != ')') i += 1;
        try out.append(alloc, line[start..i]);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Integer normalisation (R5)
// ─────────────────────────────────────────────────────────────────────────────

/// Returns the normalised decimal form, or the token unchanged if it is not a
/// bare integer literal.
pub fn normaliseInteger(alloc: Allocator, tok: []const u8) ![]const u8 {
    if (tok.len == 0) return alloc.dupe(u8, tok);
    var sign: []const u8 = "";
    var body = tok;
    if (body[0] == '-') {
        sign = "-";
        body = body[1..];
        if (body.len == 0) return alloc.dupe(u8, tok);
    }
    var base: u8 = 10;
    if (body.len > 2 and body[0] == '0' and (body[1] == 'x' or body[1] == 'X')) {
        base = 16;
        body = body[2..];
    } else if (body.len > 2 and body[0] == '0' and (body[1] == 'b' or body[1] == 'B')) {
        base = 2;
        body = body[2..];
    }
    if (body.len == 0) return alloc.dupe(u8, tok);
    var value: u128 = 0;
    var digits: usize = 0;
    for (body) |c| {
        if (c == '_') continue;
        const d: u128 = switch (c) {
            '0'...'9' => c - '0',
            'a'...'f' => c - 'a' + 10,
            'A'...'F' => c - 'A' + 10,
            else => return alloc.dupe(u8, tok), // not an integer literal
        };
        if (d >= base) return alloc.dupe(u8, tok);
        if (value > (std.math.maxInt(u128) - d) / base) return Error.BadInteger;
        value = value * base + d;
        digits += 1;
    }
    if (digits == 0) return alloc.dupe(u8, tok);
    return std.fmt.allocPrint(alloc, "{s}{d}", .{ sign, value });
}

// ─────────────────────────────────────────────────────────────────────────────
// Alpha-normalisation (R4)
// ─────────────────────────────────────────────────────────────────────────────

const pending_cap = 64;

/// Alpha-normalise a formula token list. Bound variables become `%<depth>`,
/// where depth is the binder's nesting level (0 = outermost).
pub fn alphaNormalise(alloc: Allocator, toks: []const []const u8) Error!std.ArrayListUnmanaged([]const u8) {
    const n = toks.len;
    var match = try alloc.alloc(usize, n);
    defer alloc.free(match);
    @memset(match, std.math.maxInt(usize));
    {
        var stack = std.ArrayListUnmanaged(usize).empty;
        defer stack.deinit(alloc);
        for (toks, 0..) |t, i| {
            if (std.mem.eql(u8, t, "(")) {
                stack.append(alloc, i) catch return Error.OutOfMemory;
            } else if (std.mem.eql(u8, t, ")")) {
                const open = stack.pop() orelse return Error.UnbalancedParens;
                match[open] = i;
            }
        }
        if (stack.items.len != 0) return Error.UnbalancedParens;
    }

    var out = std.ArrayListUnmanaged([]const u8).empty;
    errdefer out.deinit(alloc);
    var scope = std.ArrayListUnmanaged([]const u8).empty; // binder names, innermost last
    defer scope.deinit(alloc);
    var pending = std.ArrayListUnmanaged(usize).empty; // close index of each open binder
    defer pending.deinit(alloc);

    var i: usize = 0;
    while (i < n) {
        // Pop binders whose body has ended (close indices are monotone).
        while (pending.items.len > 0 and i > pending.items[pending.items.len - 1]) {
            _ = pending.pop();
            _ = scope.pop();
        }
        // `( forall ( x : S ) body )` with atomic S.
        const is_binder = i + 6 < n and
            std.mem.eql(u8, toks[i], "(") and
            (std.mem.eql(u8, toks[i + 1], "forall") or std.mem.eql(u8, toks[i + 1], "exists")) and
            std.mem.eql(u8, toks[i + 2], "(") and
            std.mem.eql(u8, toks[i + 4], ":") and
            match[i + 2] == i + 6;
        if (is_binder) {
            const depth = scope.items.len;
            const cname = std.fmt.allocPrint(alloc, "%{d}", .{depth}) catch return Error.OutOfMemory;
            try out.appendSlice(alloc, &[_][]const u8{ toks[i], toks[i + 1], toks[i + 2], cname, toks[i + 4], toks[i + 5], toks[i + 6] });
            scope.append(alloc, toks[i + 3]) catch return Error.OutOfMemory;
            pending.append(alloc, match[i]) catch return Error.OutOfMemory;
            i += 7;
            continue;
        }
        // If this looks like a binder but the type is not atomic, refuse: the
        // canonical form must not silently mis-scope a variable.
        const looks_binder = i + 2 < n and std.mem.eql(u8, toks[i], "(") and
            (std.mem.eql(u8, toks[i + 1], "forall") or std.mem.eql(u8, toks[i + 1], "exists"));
        if (looks_binder) return Error.MalformedBinder;

        var renamed = false;
        var s = scope.items.len;
        while (s > 0) {
            s -= 1;
            if (std.mem.eql(u8, scope.items[s], toks[i])) {
                const cname = std.fmt.allocPrint(alloc, "%{d}", .{s}) catch return Error.OutOfMemory;
                out.append(alloc, cname) catch return Error.OutOfMemory;
                renamed = true;
                break;
            }
        }
        if (!renamed) out.append(alloc, toks[i]) catch return Error.OutOfMemory;
        i += 1;
    }
    _ = pending_cap;
    return out;
}

// ─────────────────────────────────────────────────────────────────────────────
// Canonicalisation
// ─────────────────────────────────────────────────────────────────────────────

const CanonLine = struct {
    text: []u8,
    /// Head keyword (cap / assigns / field / sort).
    group: []const u8 = "",
    /// Secondary key (struct name for `field`).
    sub: []const u8 = "",
    key: u64 = 0,
};

fn lessThan(_: void, a: CanonLine, b: CanonLine) bool {
    const g = std.mem.order(u8, a.group, b.group);
    if (g != .eq) return g == .lt;
    const s = std.mem.order(u8, a.sub, b.sub);
    if (s != .eq) return s == .lt;
    if (a.key != b.key) return a.key < b.key;
    return std.mem.order(u8, a.text, b.text) == .lt;
}

fn classify(first: []const u8) enum { set_valued, positional } {
    for (set_valued) |s| {
        if (std.mem.eql(u8, first, s)) return .set_valued;
    }
    return .positional;
}

pub fn isFormulaHead(t: []const u8) bool {
    return std.mem.eql(u8, t, "requires") or std.mem.eql(u8, t, "ensures") or
        std.mem.eql(u8, t, "invariant") or std.mem.eql(u8, t, "assert");
}

/// Canonicalise a source `.cspec` file. Caller owns the returned bytes.
pub fn canonicalise(alloc: Allocator, src: []const u8) ![]u8 {
    var tokbuf = std.ArrayListUnmanaged([]const u8).empty;
    defer tokbuf.deinit(alloc);

    var positional = std.ArrayListUnmanaged([]u8).empty;
    defer positional.deinit(alloc);
    var sets = std.ArrayListUnmanaged(CanonLine).empty;
    defer sets.deinit(alloc);

    var lines = std.mem.splitScalar(u8, src, '\n');
    while (lines.next()) |raw| {
        // R1: `#` starts a comment that runs to end of line. There are no string
        // literals in the IR, so this cannot truncate payload data.
        const uncommented = if (std.mem.indexOfScalar(u8, raw, '#')) |h| raw[0..h] else raw;
        const line = std.mem.trim(u8, uncommented, " \t\r");
        if (line.len == 0) continue;
        try tokenise(alloc, line, &tokbuf);
        if (tokbuf.items.len == 0) continue;

        var owned = std.ArrayListUnmanaged([]const u8).empty;
        defer owned.deinit(alloc);

        if (isFormulaHead(tokbuf.items[0])) {
            var norm = try alphaNormalise(alloc, tokbuf.items[1..]);
            defer norm.deinit(alloc);
            try owned.append(alloc, try alloc.dupe(u8, tokbuf.items[0]));
            // R4 then R5: alpha-normalise, then normalise any integer literals.
            for (norm.items) |t| try owned.append(alloc, try normaliseInteger(alloc, t));
        } else {
            for (tokbuf.items) |t| try owned.append(alloc, try normaliseInteger(alloc, t));
        }

        const joined = try std.mem.join(alloc, " ", owned.items);
        if (classify(tokbuf.items[0]) == .positional) {
            try positional.append(alloc, joined);
        } else {
            var sub: []const u8 = "";
            var key: u64 = 0;
            if (std.mem.eql(u8, tokbuf.items[0], "field") and owned.items.len >= 3) {
                sub = owned.items[1];
                key = std.fmt.parseInt(u64, owned.items[2], 10) catch 0;
            }
            try sets.append(alloc, .{ .text = joined, .group = tokbuf.items[0], .sub = sub, .key = key });
        }
    }

    std.mem.sort(CanonLine, sets.items, {}, lessThan);

    var out = std.ArrayListUnmanaged(u8).empty;
    errdefer out.deinit(alloc);
    for (positional.items) |p| {
        try out.appendSlice(alloc, p);
        try out.append(alloc, '\n');
    }
    for (sets.items) |s| {
        try out.appendSlice(alloc, s.text);
        try out.append(alloc, '\n');
    }
    return out.toOwnedSlice(alloc);
}

pub fn canon(alloc: Allocator, src: []const u8) !Canon {
    const bytes = try canonicalise(alloc, src);
    return .{ .bytes = bytes, .digest = digestOf(domain_spec, bytes) };
}

// ─────────────────────────────────────────────────────────────────────────────
// Specification mutation operators (spec §7.3). Producing a mutant is cheap and
// deterministic; KILLING one is the VC pipeline's job (ECHIDNA). This module
// only guarantees every mutant is a distinct artifact with a distinct address,
// which is the necessary (not sufficient) half of mutation detection.
// ─────────────────────────────────────────────────────────────────────────────

pub const Mutation = enum {
    drop_last_requires,
    drop_last_ensures,
    tighten_le,
    laxen_lt,
    off_by_one,
    drop_cap,
    swap_region,
    qty_lax,
    drop_padding,
    drop_borrow,
    widen_int,

    pub fn name(self: Mutation) []const u8 {
        return @tagName(self);
    }

    pub fn all() []const Mutation {
        return &[_]Mutation{
            .drop_last_requires, .drop_last_ensures, .tighten_le, .laxen_lt,
            .off_by_one,         .drop_cap,          .swap_region, .qty_lax,
            .drop_padding,       .drop_borrow,       .widen_int,
        };
    }
};

/// Apply a mutation operator. Returns a newly allocated text, or null if the
/// operator does not apply to this specification.
pub fn applyMutation(alloc: Allocator, src: []const u8, m: Mutation) !?[]u8 {
    var line_list = std.ArrayListUnmanaged([]const u8).empty;
    defer line_list.deinit(alloc);
    var it = std.mem.splitScalar(u8, src, '\n');
    while (it.next()) |l| try line_list.append(alloc, l);

    var last_requires: ?usize = null;
    var last_ensures: ?usize = null;
    var first_cap: ?usize = null;
    var first_borrow: ?usize = null;
    var first_layout: ?usize = null;
    for (line_list.items, 0..) |l, i| {
        const t = std.mem.trim(u8, l, " \t");
        if (std.mem.startsWith(u8, t, "requires ")) last_requires = i;
        if (std.mem.startsWith(u8, t, "ensures ")) last_ensures = i;
        if (first_cap == null and std.mem.startsWith(u8, t, "cap ")) first_cap = i;
        if (first_borrow == null and std.mem.startsWith(u8, t, "borrow ")) first_borrow = i;
        if (first_layout == null and std.mem.startsWith(u8, t, "layout ")) first_layout = i;
    }

    var out = std.ArrayListUnmanaged(u8).empty;
    errdefer out.deinit(alloc);
    var mutated_any = false;

    for (line_list.items, 0..) |l, i| {
        var text: []const u8 = l;
        var rewritten: ?[]u8 = null;
        var dropped = false;
        switch (m) {
            .drop_last_requires => if (last_requires != null and last_requires.? == i) {
                dropped = true;
                mutated_any = true;
            },
            .drop_last_ensures => if (last_ensures != null and last_ensures.? == i) {
                dropped = true;
                mutated_any = true;
            },
            .drop_cap => if (first_cap != null and first_cap.? == i) {
                dropped = true;
                mutated_any = true;
            },
            .drop_borrow => if (first_borrow != null and first_borrow.? == i) {
                dropped = true;
                mutated_any = true;
            },
            .tighten_le => if (std.mem.indexOf(u8, l, "( <= ") != null) {
                rewritten = try replaceAllIn(alloc, l, "( <= ", "( < ");
                mutated_any = true;
            },
            .laxen_lt => if (std.mem.indexOf(u8, l, "( < ") != null) {
                rewritten = try replaceAllIn(alloc, l, "( < ", "( <= ");
                mutated_any = true;
            },
            .off_by_one => if (last_ensures != null and last_ensures.? == i) {
                if (try incrementFirstInt(alloc, l)) |r| {
                    rewritten = r;
                    mutated_any = true;
                }
            },
            .swap_region => if (std.mem.indexOf(u8, l, "r0") != null) {
                rewritten = try replaceAllIn(alloc, l, "r0", "r1");
                mutated_any = true;
            },
            .qty_lax => if (std.mem.startsWith(u8, std.mem.trim(u8, l, " \t"), "param ")) {
                if (try loosenQuantity(alloc, l)) |r| {
                    rewritten = r;
                    mutated_any = true;
                }
            },
            .drop_padding => if (first_layout != null and first_layout.? == i) {
                if (try stripPadding(alloc, l)) |r| {
                    rewritten = r;
                    mutated_any = true;
                }
            },
            .widen_int => if (std.mem.indexOf(u8, l, "u16") != null) {
                rewritten = try replaceAllIn(alloc, l, "u16", "u32");
                mutated_any = true;
            },
        }
        if (dropped) {
            // Remove the line entirely: also swallow one adjacent newline.
            continue;
        }
        if (rewritten) |r| text = r;
        try out.appendSlice(alloc, text);
        try out.append(alloc, '\n');
    }
    if (!mutated_any) {
        out.deinit(alloc);
        return null;
    }
    return try out.toOwnedSlice(alloc);
}

fn replaceAllIn(alloc: Allocator, src: []const u8, needle: []const u8, repl: []const u8) ![]u8 {
    var out = std.ArrayListUnmanaged(u8).empty;
    errdefer out.deinit(alloc);
    var i: usize = 0;
    while (i < src.len) {
        if (std.mem.startsWith(u8, src[i..], needle)) {
            try out.appendSlice(alloc, repl);
            i += needle.len;
        } else {
            try out.append(alloc, src[i]);
            i += 1;
        }
    }
    return try out.toOwnedSlice(alloc);
}

fn incrementFirstInt(alloc: Allocator, src: []const u8) !?[]u8 {
    var i: usize = 0;
    while (i < src.len) : (i += 1) {
        if (src[i] >= '0' and src[i] <= '9') {
            const start = i;
            while (i < src.len and src[i] >= '0' and src[i] <= '9') i += 1;
            const v = std.fmt.parseInt(u64, src[start..i], 10) catch continue;
            var out = std.ArrayListUnmanaged(u8).empty;
            errdefer out.deinit(alloc);
            try out.appendSlice(alloc, src[0..start]);
            const digits = try std.fmt.allocPrint(alloc, "{d}", .{v + 1});
            try out.appendSlice(alloc, digits);
            try out.appendSlice(alloc, src[i..]);
            return try out.toOwnedSlice(alloc);
        }
    }
    return null;
}

fn loosenQuantity(alloc: Allocator, line: []const u8) !?[]u8 {
    var toks = std.ArrayListUnmanaged([]const u8).empty;
    defer toks.deinit(alloc);
    try tokenise(alloc, line, &toks);
    if (toks.items.len < 4) return null;
    if (!std.mem.eql(u8, toks.items[2], "1")) return null;
    var out = std.ArrayListUnmanaged(u8).empty;
    errdefer out.deinit(alloc);
    for (toks.items, 0..) |t, idx| {
        if (idx != 0) try out.append(alloc, ' ');
        if (idx == 2) try out.appendSlice(alloc, "W") else try out.appendSlice(alloc, t);
    }
    return try out.toOwnedSlice(alloc);
}

fn stripPadding(alloc: Allocator, line: []const u8) !?[]u8 {
    var toks = std.ArrayListUnmanaged([]const u8).empty;
    defer toks.deinit(alloc);
    try tokenise(alloc, line, &toks);
    if (toks.items.len < 5) return null;
    var out = std.ArrayListUnmanaged(u8).empty;
    errdefer out.deinit(alloc);
    var k: usize = 0;
    while (k < 5) : (k += 1) {
        if (k != 0) try out.append(alloc, ' ');
        try out.appendSlice(alloc, toks.items[k]);
    }
    try out.appendSlice(alloc, " -");
    return try out.toOwnedSlice(alloc);
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

const testing = std.testing;
const ta = std.heap.page_allocator;

test "blake3 known-answer" {
    try testing.expectEqualStrings(
        "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85",
        &digestHex("", "abc"),
    );
}

// R8 is a claim about *domain separation*: the same bytes hashed in two roles
// must not collide. This is cheap to test and the failure mode (a witness hash
// equal to a spec hash) would be silent, so it is tested rather than assumed.
test "domains separate" {
    const bytes = "cspec 1\ncontract x\n";
    const spec = digestHex(domain_spec, bytes);
    const vc = digestHex(domain_vc, bytes);
    const dk = digestHex(domain_dk, bytes);
    const src = digestHex(domain_src, bytes);
    try testing.expect(!std.mem.eql(u8, &spec, &vc));
    try testing.expect(!std.mem.eql(u8, &spec, &dk));
    try testing.expect(!std.mem.eql(u8, &spec, &src));
    try testing.expect(!std.mem.eql(u8, &vc, &dk));
    try testing.expect(!std.mem.eql(u8, &vc, &src));
    try testing.expect(!std.mem.eql(u8, &dk, &src));
}

test "integer normalisation" {
    try testing.expectEqualStrings("16", try normaliseInteger(ta, "0x10"));
    try testing.expectEqualStrings("1000", try normaliseInteger(ta, "1_000"));
    try testing.expectEqualStrings("255", try normaliseInteger(ta, "0b11111111"));
    try testing.expectEqualStrings("in.len", try normaliseInteger(ta, "in.len"));
    try testing.expectEqualStrings("-3", try normaliseInteger(ta, "-0x3"));
}

test "alpha-normalisation is insensitive to binder names" {
    var t1 = std.ArrayListUnmanaged([]const u8).empty;
    try tokenise(ta, "( forall ( i : u16 ) ( < i 65535 ) )", &t1);
    const n1 = try alphaNormalise(ta, t1.items);
    var t2 = std.ArrayListUnmanaged([]const u8).empty;
    try tokenise(ta, "( forall ( k : u16 ) ( < k 65535 ) )", &t2);
    const n2 = try alphaNormalise(ta, t2.items);
    try testing.expectEqualStrings(
        try std.mem.join(ta, " ", n1.items),
        try std.mem.join(ta, " ", n2.items),
    );
    try testing.expectEqualStrings("( forall ( %0 : u16 ) ( < %0 65535 ) )", try std.mem.join(ta, " ", n1.items));
}

test "compound binder types are rejected, not mis-scoped" {
    var t = std.ArrayListUnmanaged([]const u8).empty;
    try tokenise(ta, "( forall ( i : ( array u8 4 ) ) ( < i 4 ) )", &t);
    try testing.expectError(Error.MalformedBinder, alphaNormalise(ta, t.items));
}

test "set lines are sorted, positional lines keep their order" {
    const src = "cspec 1\ncontract demo.parse\nparam h 1 handle\nparam buf 0 slice\n" ++
        "cap Fs\ncap Alloc\nrequires ( <= n 8 )\nrequires ( <= m 4 )\n" ++
        "field H 8 4 crc u32\nfield H 0 2 magic u16\n";
    const expected = "cspec 1\ncontract demo.parse\nparam h 1 handle\nparam buf 0 slice\n" ++
        "requires ( <= n 8 )\nrequires ( <= m 4 )\ncap Alloc\ncap Fs\n" ++
        "field H 0 2 magic u16\nfield H 8 4 crc u32\n";
    const out = try canonicalise(ta, src);
    try testing.expectEqualStrings(expected, out);
}

test "comments, blank lines and whitespace do not affect the digest" {
    const c1 = try canon(ta, "cspec 1\ncontract x\n");
    const c2 = try canon(ta, "# hello\n\ncspec 1   \n\ncontract x   # trailing\n");
    try testing.expectEqualSlices(u8, &c1.digest, &c2.digest);
}

test "a one-token change changes the digest" {
    const c1 = try canon(ta, "cspec 1\nrequires ( < len 8 )\n");
    const c2 = try canon(ta, "cspec 1\nrequires ( <= len 8 )\n");
    try testing.expect(!std.mem.eql(u8, &c1.digest, &c2.digest));
}

test "every mutation operator yields a distinct artifact" {
    const src = "cspec 1\ncontract demo.parse\nparam h 1 handle\n" ++
        "borrow buf shr r0 slice\nlayout H x86_64 24 8 6..8,12..16\n" ++
        "param n 0 u16\nrequires ( <= len 65535 )\nrequires ( < len n )\nensures ( <= ( + len 10 ) ( len in ) )\ncap Alloc\n";
    const base = try canon(ta, src);
    const basehex = base.hex();
    var seen: [16][64]u8 = undefined;
    var seen_n: usize = 0;
    seen[seen_n] = basehex;
    seen_n += 1;
    var applied: usize = 0;
    for (Mutation.all()) |m| {
        const maybe = try applyMutation(ta, src, m);
        if (maybe) |mut| {
            const c = try canon(ta, mut);
            const hx = c.hex();
            try testing.expect(!std.mem.eql(u8, &basehex, &hx));
            for (seen[0..seen_n]) |prev| {
                try testing.expect(!std.mem.eql(u8, &prev, &hx));
            }
            seen[seen_n] = hx;
            seen_n += 1;
            applied += 1;
        }
    }
    try testing.expectEqual(@as(usize, 11), applied);
}
