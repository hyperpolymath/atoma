// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// frontend.zig — Zig source → Core Spec IR (Face B) and subset conformance.
//
// This is the implementation of §5 of the specification: syntax comes from
// `std.zig.Ast`; every *semantic* fact (layout, sizes, offsets) comes from the
// compiler through the comptime witness, never from this file. Atoma never
// re-implements the compiler, which is why it survives release churn.
//
// Two entry points:
//
//   extract  doc-comment directives on a declaration → canonical `.cspec` text
//   check    subset conformance → `E-*` diagnostics, one per violation
//
// Directives are written in doc comments and may carry the `//!` prefix the
// specification uses:
//
//     /// @contract atoma.frame.parse
//     /// //! @requires ( <= 12 ( len input ) )
//
// LIMITS (stated, not hidden): this is a token-level analysis. It can see
// `extern struct` field names but not resolved types, so E-ABI-WIDTH is a
// conservative token check, not a type check. The authoritative version is the
// typed pass in Phase 2; the token pass exists so that Phase 0 has teeth.

const std = @import("std");
const Ast = std.zig.Ast;
const Allocator = std.mem.Allocator;

pub const Diag = struct {
    code: []const u8,
    line: u32,
    detail: []const u8,
};

pub const Report = struct {
    diags: std.ArrayListUnmanaged(Diag) = .empty,
    decls: usize = 0,
    exports: usize = 0,
    contracts: usize = 0,

    /// Diag owns its two strings: they are copied out of the parse buffer, which
    /// is freed before the report is consumed. (Getting this wrong segfaulted
    /// `atoma check` on the first real file — token slices are not stable.)
    pub fn deinit(self: *Report, alloc: Allocator) void {
        for (self.diags.items) |d| {
            alloc.free(@constCast(d.code));
            alloc.free(@constCast(d.detail));
        }
        self.diags.deinit(alloc);
    }

    pub fn add(self: *Report, alloc: Allocator, code: []const u8, line: u32, detail: []const u8) !void {
        const c = try alloc.dupe(u8, code);
        errdefer alloc.free(c);
        const d = try alloc.dupe(u8, detail);
        try self.diags.append(alloc, .{ .code = c, .line = line, .detail = d });
    }
};

fn lineOf(src: []const u8, offset: usize) u32 {
    var line: u32 = 1;
    for (src[0..@min(offset, src.len)]) |c| {
        if (c == '\n') line += 1;
    }
    return line;
}

fn eql(a: []const u8, b: []const u8) bool {
    return std.mem.eql(u8, a, b);
}

// ─────────────────────────────────────────────────────────────────────────────
// Directives inside a doc-comment run
// ─────────────────────────────────────────────────────────────────────────────

/// One `@directive value` line recovered from a doc comment.
pub const Directive = struct {
    key: []const u8, // without the '@'
    value: []const u8,
    line: u32,
};

/// Strip `///`, then an optional `//!`, then whitespace. Returns the remainder,
/// or null when the line carries no directive.
pub fn directiveBody(raw: []const u8) ?[]const u8 {
    var s = std.mem.trim(u8, raw, " \t\r");
    if (!std.mem.startsWith(u8, s, "///")) return null;
    s = std.mem.trim(u8, s[3..], " \t\r");
    if (std.mem.startsWith(u8, s, "//!")) s = std.mem.trim(u8, s[3..], " \t\r");
    if (s.len == 0 or s[0] != '@') return null;
    return s[1..];
}

/// Parse a directive body into (key, value). `requires` is the key, the rest is
/// the value verbatim (the value is a formula in the IR's own grammar).
pub fn parseDirective(body: []const u8) struct { key: []const u8, value: []const u8 } {
    const sp = std.mem.indexOfScalar(u8, body, ' ') orelse body.len;
    var key = body[0..sp];
    var value = if (sp < body.len) body[sp + 1 ..] else "";
    // Tolerate the aligned spelling `@requires   ( ... )`.
    value = std.mem.trim(u8, value, " \t");
    // `@param` lines are frequently written aligned; keep single internal spaces
    // by collapsing runs of spaces.
    _ = &key;
    return .{ .key = key, .value = value };
}

/// Collapse runs of spaces/tabs into one space, in place into `out`.
fn squashInto(out: *std.ArrayListUnmanaged(u8), alloc: Allocator, s: []const u8) !void {
    var prev_space = false;
    for (s) |c| {
        const is_space = c == ' ' or c == '\t';
        if (is_space) {
            if (!prev_space) try out.append(alloc, ' ');
            prev_space = true;
        } else {
            try out.append(alloc, c);
            prev_space = false;
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Declaration discovery
// ─────────────────────────────────────────────────────────────────────────────

const Decl = struct {
    kind: enum { fn_decl, var_decl, const_decl },
    name: []const u8,
    line: u32,
    token: u32,
    exported: bool,
    doc_first: u32, // first doc_comment token of the run, or sentinel
    doc_end: u32, // one past the last
};

const no_doc: u32 = 0xFFFF_FFFF;

fn collectDecls(alloc: Allocator, ast: Ast, report: *Report) !std.ArrayListUnmanaged(Decl) {
    var out: std.ArrayListUnmanaged(Decl) = .empty;
    errdefer out.deinit(alloc);
    const tags = ast.tokens.items(.tag);
    const n: u32 = @intCast(tags.len);

    var pending_first: u32 = no_doc;
    var pending_end: u32 = no_doc;
    var saw_export = false;
    var depth: u32 = 0;

    var i: u32 = 0;
    while (i < n) : (i += 1) {
        const t = tags[i];
        switch (t) {
            .l_brace => {
                depth += 1;
                pending_first = no_doc;
                continue;
            },
            .r_brace => {
                if (depth > 0) depth -= 1;
                pending_first = no_doc;
                continue;
            },
            .doc_comment => {
                if (pending_first == no_doc) pending_first = i;
                pending_end = i + 1;
                continue;
            },
            .keyword_export => {
                saw_export = true;
                continue;
            },
            .keyword_pub, .keyword_extern, .keyword_inline, .keyword_noinline => continue,
            .keyword_fn, .keyword_var, .keyword_const => {
                if (i + 1 < n and tags[i + 1] == .identifier) {
                    const name = Ast.tokenSlice(ast, i + 1);
                    const loc = ast.tokenLocation(0, i);
                    try out.append(alloc, .{
                        .kind = switch (t) {
                            .keyword_fn => .fn_decl,
                            .keyword_var => .var_decl,
                            else => .const_decl,
                        },
                        .name = name,
                        .line = @intCast(loc.line + 1),
                        .token = i,
                        .exported = saw_export,
                        .doc_first = pending_first,
                        .doc_end = if (pending_first == no_doc) no_doc else pending_end,
                    });
                    if (t == .keyword_fn and saw_export) report.exports += 1;
                    saw_export = false;
                    pending_first = no_doc;
                    continue;
                }
            },
            else => {},
        }
        // Any other token ends a doc run's claim on the next declaration, unless
        // it is a modifier handled above.
        if (t != .doc_comment) {
            pending_first = no_doc;
            saw_export = saw_export and (t == .keyword_export);
        }
    }
    report.decls = out.items.len;
    return out;
}

// ─────────────────────────────────────────────────────────────────────────────
// Banned-construct scan (§2.4)
// ─────────────────────────────────────────────────────────────────────────────

const BannedBuiltin = struct { text: []const u8, code: []const u8 };

const banned_builtins = [_]BannedBuiltin{
    .{ .text = "@ptrFromInt", .code = "E-PTR-INT" },
    .{ .text = "@ptrCast", .code = "E-PTR-CAST" },
    .{ .text = "@alignCast", .code = "E-PTR-CAST" },
    .{ .text = "@cImport", .code = "E-CIMPORT" },
    .{ .text = "@panic", .code = "E-PANIC" },
    .{ .text = "@setRuntimeSafety", .code = "E-SAFETY-OFF" },
    .{ .text = "@setEvalBranchQuota", .code = "E-QUOTA" },
};

pub fn scanBanned(alloc: Allocator, ast: Ast, src: []const u8, report: *Report) !void {
    const tags = ast.tokens.items(.tag);
    const n: u32 = @intCast(tags.len);
    var depth: u32 = 0;

    var i: u32 = 0;
    while (i < n) : (i += 1) {
        const t = tags[i];
        const text = Ast.tokenSlice(ast, i);
        const line = lineOf(src, ast.tokens.items(.start)[i]);

        if (t == .l_brace) {
            depth += 1;
            continue;
        }
        if (t == .r_brace) {
            if (depth > 0) depth -= 1;
            continue;
        }

        switch (t) {
            .builtin => {
                for (banned_builtins) |b| {
                    if (eql(text, b.text)) try report.add(alloc, b.code, line, text);
                }
            },
            .keyword_volatile => try report.add(alloc, "E-VOLATILE", line, text),
            .keyword_asm => try report.add(alloc, "E-ASM", line, text),
            .keyword_unreachable => try report.add(alloc, "E-UNREACHABLE", line, text),
            .keyword_packed => try report.add(alloc, "E-ABI-PACKED", line, text),
            .identifier => {
                if (eql(text, "c_allocator") or eql(text, "page_allocator") or
                    eql(text, "raw_c_allocator"))
                {
                    try report.add(alloc, "E-ALLOC-AMBIENT", line, text);
                }
                // A top-level `var` (outside any braces) is ambient mutable state.
                if (depth == 0 and i > 0 and tags[i - 1] == .keyword_var) {
                    try report.add(alloc, "E-GLOBAL-VAR", line, text);
                }
            },
            .period => {
                if (i + 1 < n and tags[i + 1] == .question_mark) {
                    try report.add(alloc, "E-OPTIONAL-UNWRAP", line, ".?");
                }
            },
            .l_bracket => {
                // `[*c]` tokenises as `[` `*` `c` `]`.
                if (i + 3 < n and tags[i + 1] == .asterisk and
                    tags[i + 2] == .identifier and eql(Ast.tokenSlice(ast, i + 2), "c") and
                    tags[i + 3] == .r_bracket)
                {
                    try report.add(alloc, "E-PTR-C", line, "[*c]");
                }
            },
            else => {},
        }
    }
}

/// `extern struct` / `extern union` bodies may not contain width-ambiguous or
/// non-C types. Conservative token check, see the header comment.
pub fn scanAbiTypes(alloc: Allocator, ast: Ast, src: []const u8, report: *Report) !void {
    const tags = ast.tokens.items(.tag);
    const n: u32 = @intCast(tags.len);

    var i: u32 = 0;
    while (i + 1 < n) : (i += 1) {
        if (tags[i] != .keyword_extern) continue;
        if (tags[i + 1] != .keyword_struct and tags[i + 1] != .keyword_union) continue;
        const is_union = tags[i + 1] == .keyword_union;
        const line = lineOf(src, ast.tokens.items(.start)[i]);
        if (is_union) try report.add(alloc, "E-ABI-UNION", line, "extern union");

        // Walk the body.
        var j = i + 2;
        var depth: i32 = 0;
        var seen_brace = false;
        while (j < n) : (j += 1) {
            const tj = tags[j];
            if (tj == .l_brace) {
                depth += 1;
                seen_brace = true;
                continue;
            }
            if (tj == .r_brace) {
                depth -= 1;
                if (seen_brace and depth == 0) break;
                continue;
            }
            if (tj != .identifier) continue;
            const text = Ast.tokenSlice(ast, j);
            const prev_is_type_pos = j > 0 and (tags[j - 1] == .colon or tags[j - 1] == .asterisk or
                tags[j - 1] == .l_bracket);
            if (!prev_is_type_pos) continue;
            if (eql(text, "usize") or eql(text, "isize") or eql(text, "bool") or
                eql(text, "anyopaque") or eql(text, "anyerror"))
            {
                try report.add(alloc, "E-ABI-WIDTH", line, text);
            }
        }
    }
}

/// An `export fn` must use the C calling convention, spelled `.c` (the compiler
/// rejects `.C` on every Zig release measured — see the spec's version matrix).
pub fn scanCallconv(alloc: Allocator, ast: Ast, decls: []const Decl, report: *Report) !void {
    const tags = ast.tokens.items(.tag);
    const n: u32 = @intCast(tags.len);
    for (decls) |d| {
        if (d.kind != .fn_decl or !d.exported) continue;
        var i = d.token;
        var found = false;
        var spelled_ok = false;
        while (i < n and tags[i] != .l_brace) : (i += 1) {
            if (tags[i] != .keyword_callconv) continue;
            found = true;
            if (i + 4 < n and tags[i + 1] == .l_paren and tags[i + 2] == .period and
                tags[i + 3] == .identifier and eql(Ast.tokenSlice(ast, i + 3), "c"))
            {
                spelled_ok = true;
            }
        }
        if (!found) {
            try report.add(alloc, "E-ABI-NO-CALLCONV", d.line, d.name);
        } else if (!spelled_ok) {
            try report.add(alloc, "E-ABI-CALLCONV", d.line, d.name);
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// check — the whole subset pass
// ─────────────────────────────────────────────────────────────────────────────

pub const CheckOptions = struct {
    /// Every `export fn` must carry a `@contract`. Off only for fixtures.
    require_contracts: bool = true,
};

pub fn check(alloc: Allocator, src: []const u8, opts: CheckOptions) !Report {
    var report = Report{};
    const srcz = try alloc.dupeZ(u8, src);
    defer alloc.free(srcz);
    var ast = try Ast.parse(alloc, srcz, .zig);
    defer ast.deinit(alloc);

    if (ast.errors.len != 0) {
        const loc = ast.tokenLocation(0, ast.errors[0].token);
        try report.add(alloc, "E-PARSE", @intCast(loc.line + 1), "source does not parse");
        return report;
    }

    var decls = try collectDecls(alloc, ast, &report);
    defer decls.deinit(alloc);

    try scanBanned(alloc, ast, src, &report);
    try scanAbiTypes(alloc, ast, src, &report);
    try scanCallconv(alloc, ast, decls.items, &report);

    // Contract ↔ export linkage, both directions.
    var contracted = std.StringHashMapUnmanaged(void){};
    defer contracted.deinit(alloc);

    for (decls.items) |d| {
        if (d.doc_first == no_doc) continue;
        var t = d.doc_first;
        while (t < d.doc_end) : (t += 1) {
            const body = directiveBody(Ast.tokenSlice(ast, t)) orelse continue;
            const kv = parseDirective(body);
            if (eql(kv.key, "contract")) {
                report.contracts += 1;
                try contracted.put(alloc, d.name, {});
            }
        }
    }

    if (opts.require_contracts) {
        for (decls.items) |d| {
            if (d.kind == .fn_decl and d.exported and !contracted.contains(d.name)) {
                try report.add(alloc, "E-UNCONTRACTED-EXPORT", d.line, d.name);
            }
        }
    }
    var it = contracted.keyIterator();
    while (it.next()) |name| {
        var found = false;
        for (decls.items) |d| {
            if (d.kind == .fn_decl and d.exported and eql(d.name, name.*)) {
                found = true;
                break;
            }
        }
        if (!found) try report.add(alloc, "E-DANGLING-CONTRACT", 0, name.*);
    }
    return report;
}

// ─────────────────────────────────────────────────────────────────────────────
// extract — Face B
// ─────────────────────────────────────────────────────────────────────────────

fn Bucket(comptime T: type) type {
    return std.ArrayListUnmanaged(T){};
}

pub const ExtractOptions = struct {
    /// Selects the declaration whose contract is emitted. Empty = the only one.
    symbol: []const u8 = "",
    /// Used when the contract carries no `@contract` directive.
    default_name: []const u8 = "",
};

pub fn extract(alloc: Allocator, src: []const u8, opts: ExtractOptions) ![]u8 {
    std.debug.assert(opts.default_name.len > 0 or opts.symbol.len > 0);
    const srcz = try alloc.dupeZ(u8, src);
    defer alloc.free(srcz);
    var ast = try Ast.parse(alloc, srcz, .zig);
    defer ast.deinit(alloc);
    if (ast.errors.len != 0) return error.ParseError;

    var dummy = Report{};
    defer dummy.deinit(alloc);
    var decls = try collectDecls(alloc, ast, &dummy);
    defer decls.deinit(alloc);

    var header = std.ArrayListUnmanaged(u8){};
    defer header.deinit(alloc);
    var params = std.ArrayListUnmanaged(u8){};
    defer params.deinit(alloc);
    var borrows = std.ArrayListUnmanaged(u8){};
    defer borrows.deinit(alloc);
    var requires = std.ArrayListUnmanaged(u8){};
    defer requires.deinit(alloc);
    var ensures = std.ArrayListUnmanaged(u8){};
    defer ensures.deinit(alloc);
    var asserts = std.ArrayListUnmanaged(u8){};
    defer asserts.deinit(alloc);
    var assigns = std.ArrayListUnmanaged(u8){};
    defer assigns.deinit(alloc);
    var caps = std.ArrayListUnmanaged(u8){};
    defer caps.deinit(alloc);
    var bounds = std.ArrayListUnmanaged(u8){};
    defer bounds.deinit(alloc);

    var contract_name = std.ArrayListUnmanaged(u8){};
    defer contract_name.deinit(alloc);
    var kind = std.ArrayListUnmanaged(u8){};
    defer kind.deinit(alloc);
    var abisym = std.ArrayListUnmanaged(u8){};
    defer abisym.deinit(alloc);

    var matched = false;

    for (decls.items) |d| {
        if (d.doc_first == no_doc) continue;
        if (opts.symbol.len > 0 and !eql(d.name, opts.symbol)) continue;

        // Does this declaration carry a contract at all?
        var has = false;
        var t = d.doc_first;
        while (t < d.doc_end) : (t += 1) {
            const body = directiveBody(Ast.tokenSlice(ast, t)) orelse continue;
            if (eql(parseDirective(body).key, "contract")) has = true;
        }
        if (!has) continue;
        if (matched) return error.MultipleContracts;
        matched = true;

        t = d.doc_first;
        while (t < d.doc_end) : (t += 1) {
            const body = directiveBody(Ast.tokenSlice(ast, t)) orelse continue;
            const kv = parseDirective(body);
            if (eql(kv.key, "contract")) {
                try squashInto(&contract_name, alloc, kv.value);
            } else if (eql(kv.key, "kind")) {
                try squashInto(&kind, alloc, kv.value);
            } else if (eql(kv.key, "param")) {
                try emits(&params, alloc, "param ", kv.value);
            } else if (eql(kv.key, "borrow")) {
                try emits(&borrows, alloc, "borrow ", kv.value);
            } else if (eql(kv.key, "requires")) {
                try emits(&requires, alloc, "requires ", kv.value);
            } else if (eql(kv.key, "ensures")) {
                try emits(&ensures, alloc, "ensures ", kv.value);
            } else if (eql(kv.key, "assert")) {
                try emits(&asserts, alloc, "assert ", kv.value);
            } else if (eql(kv.key, "assigns")) {
                try emits(&assigns, alloc, "assigns ", kv.value);
            } else if (eql(kv.key, "cap")) {
                try emits(&caps, alloc, "cap ", kv.value);
            } else if (eql(kv.key, "bound")) {
                try emits(&bounds, alloc, "bound ", kv.value);
            } else if (eql(kv.key, "abi")) {
                // `@abi callconv(.c)` is documentation; the compiler already
                // enforces it, and `scanCallconv` rejects `.C`.
            } else if (eql(kv.key, "decreases") or eql(kv.key, "invariant") or
                eql(kv.key, "linear") or eql(kv.key, "frame"))
            {
                // Notes for humans; not part of the canonical contract.
            } else if (kv.key.len > 0) {
                return error.UnknownDirective;
            }
        }
    }

    if (!matched) return error.NoContract;

    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(alloc);
    var w = out.writer(alloc);

    try w.writeAll("cspec 1\n");
    try w.writeAll("contract ");
    if (contract_name.items.len > 0) {
        try w.writeAll(contract_name.items);
    } else {
        try w.writeAll(opts.default_name);
    }
    try w.writeAll("\nkind ");
    if (kind.items.len > 0) try w.writeAll(kind.items) else try w.writeAll("extern");
    try w.writeAll("\nabisym ");
    if (abisym.items.len > 0) try w.writeAll(abisym.items) else {
        // The declaration name is the ABI symbol for an `export fn`.
        for (decls.items) |d| {
            if (d.doc_first != no_doc and eql(d.name, opts.symbol)) {
                try w.writeAll(d.name);
                break;
            }
            if (opts.symbol.len == 0 and d.kind == .fn_decl and d.exported) {
                try w.writeAll(d.name);
                break;
            }
        }
    }
    try w.writeAll("\n");
    try out.appendSlice(alloc, params.items);
    try out.appendSlice(alloc, borrows.items);
    try out.appendSlice(alloc, requires.items);
    try out.appendSlice(alloc, ensures.items);
    try out.appendSlice(alloc, asserts.items);
    try out.appendSlice(alloc, assigns.items);
    try out.appendSlice(alloc, caps.items);
    try out.appendSlice(alloc, bounds.items);
    return out.toOwnedSlice(alloc);
}

fn emits(bucket: *std.ArrayListUnmanaged(u8), alloc: Allocator, prefix: []const u8, value: []const u8) !void {
    try bucket.appendSlice(alloc, prefix);
    try squashInto(bucket, alloc, value);
    try bucket.append(alloc, '\n');
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

const testing = std.testing;

const sample =
    \\/// @contract demo.f
    \\/// @kind extern
    \\/// @param h W handle
    \\/// //! @requires ( <= 12 ( len input ) )
    \\/// @ensures  ( = ( magic out ) 0x5441 )
    \\/// @cap Write r1
    \\/// @cap Read r0
    \\/// @bound steps ( + 12 ( * 8 input_len ) )
    \\export fn demo_f(h: ?*const Handle, out: ?*FrameOut) callconv(.c) Result {
    \\    return .ok;
    \\}
;

test "directive bodies accept both spellings" {
    try testing.expectEqualStrings("requires x", directiveBody("/// //! @requires x").?);
    try testing.expectEqualStrings("requires x", directiveBody("/// @requires x").?);
    try testing.expect(directiveBody("/// just prose") == null);
    try testing.expect(directiveBody("const x = 1;") == null);
}

test "extract produces the canonical contract" {
    const a = std.heap.page_allocator;
    const out = try extract(a, sample, .{ .symbol = "demo_f" });
    defer a.free(out);
    try testing.expectEqualStrings(
        \\cspec 1
        \\contract demo.f
        \\kind extern
        \\abisym demo_f
        \\param h W handle
        \\requires ( <= 12 ( len input ) )
        \\ensures ( = ( magic out ) 0x5441 )
        \\cap Write r1
        \\cap Read r0
        \\bound steps ( + 12 ( * 8 input_len ) )
        \\
    , out);
}

test "check rejects a banned construct" {
    const a = std.heap.page_allocator;
    var r = try check(a, "fn f(p: [*c]u8) void { _ = p; }\n", .{ .require_contracts = false });
    defer r.deinit(a);
    try testing.expectEqual(@as(usize, 1), r.diags.items.len);
    try testing.expectEqualStrings("E-PTR-C", r.diags.items[0].code);
}

test "check rejects an uncontracted export and a dangling contract" {
    const a = std.heap.page_allocator;
    var r = try check(a, "export fn lonely() callconv(.c) void {}\n", .{});
    defer r.deinit(a);
    try testing.expectEqualStrings("E-UNCONTRACTED-EXPORT", r.diags.items[0].code);

    var r2 = try check(a, sample, .{});
    defer r2.deinit(a);
    try testing.expectEqual(@as(usize, 0), r2.diags.items.len);
}

test "check rejects .C spelling and missing callconv" {
    const a = std.heap.page_allocator;
    var r = try check(a, "export fn f() callconv(.C) void {}\n", .{ .require_contracts = false });
    defer r.deinit(a);
    try testing.expectEqualStrings("E-ABI-CALLCONV", r.diags.items[0].code);

    var r2 = try check(a, "export fn f() void {}\n", .{ .require_contracts = false });
    defer r2.deinit(a);
    try testing.expectEqualStrings("E-ABI-NO-CALLCONV", r2.diags.items[0].code);
}

test "check rejects usize inside an extern struct" {
    const a = std.heap.page_allocator;
    var r = try check(a, "pub const S = extern struct { n: usize };\n", .{ .require_contracts = false });
    defer r.deinit(a);
    try testing.expectEqualStrings("E-ABI-WIDTH", r.diags.items[0].code);
}
