// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Experimental source-bound u8 pilot. This is deliberately a closed language:
//! one export, one u8 input, one return, and an equality postcondition. Anything
//! else is refused. Parsing/lowering and this evaluator are still trusted;
//! finite enumeration is evidence, not a kernel-checked refinement theorem.
const std = @import("std");
const Allocator = std.mem.Allocator;
const Ast = std.zig.Ast;

pub const Expr = union(enum) {
    input,
    literal: u8,
    add_wrap: u8,

    pub fn eval(self: Expr, x: u8) u8 {
        return switch (self) {
            .input => x,
            .literal => |n| n,
            .add_wrap => |n| x +% n,
        };
    }

    fn smt(self: Expr, w: *std.Io.Writer) !void {
        switch (self) {
            .input => try w.writeAll("x"),
            .literal => |n| try w.print("(_ bv{d} 8)", .{n}),
            .add_wrap => |n| try w.print("(bvadd x (_ bv{d} 8))", .{n}),
        }
    }
};

pub const Program = struct {
    body: Expr,
    ensures_add: u8,
    source_hash: [32]u8,

    pub fn counterexample(self: Program) ?u8 {
        for (0..256) |i| {
            const x: u8 = @intCast(i);
            if (self.body.eval(x) != x +% self.ensures_add) return x;
        }
        return null;
    }

    pub fn emit(self: Program, w: *std.Io.Writer) !void {
        const hash = std.fmt.bytesToHex(self.source_hash, .lower);
        try w.print("; atoma.source.u8.v1 source-blake3:{s}\n", .{hash});
        try w.writeAll("; Warrant only: frontend and compiler refinement remain trusted\n(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n(assert (not (= ");
        try self.body.smt(w);
        try w.print(" (bvadd x (_ bv{d} 8)))))\n(check-sat)\n", .{self.ensures_add});
    }
};

const Cursor = struct {
    ast: *const Ast,
    pos: u32 = 0,

    fn text(self: *Cursor) []const u8 {
        return self.ast.tokenSlice(self.pos);
    }
    fn take(self: *Cursor, want: []const u8) !void {
        if (!std.mem.eql(u8, self.text(), want)) return error.UnsupportedSource;
        self.pos += 1;
    }
    fn ident(self: *Cursor) ![]const u8 {
        if (self.ast.tokens.items(.tag)[self.pos] != .identifier) return error.UnsupportedSource;
        const name = self.text();
        // No quoted identifiers or builtin/type shadowing in this pilot.
        if (name.len == 0 or name[0] == '@' or std.mem.eql(u8, name, "_") or std.zig.isPrimitive(name)) return error.UnsupportedSource;
        self.pos += 1;
        return name;
    }
    fn number(self: *Cursor) !u8 {
        if (self.ast.tokens.items(.tag)[self.pos] != .number_literal) return error.UnsupportedSource;
        const n = std.fmt.parseInt(u8, self.text(), 0) catch return error.UnsupportedSource;
        self.pos += 1;
        return n;
    }
};

pub fn lower(alloc: Allocator, src: []const u8) !Program {
    const srcz = try alloc.dupeZ(u8, src);
    defer alloc.free(srcz);
    var ast = try Ast.parse(alloc, srcz, .zig);
    defer ast.deinit(alloc);
    if (ast.errors.len != 0) return error.ParseError;
    var c = Cursor{ .ast = &ast };
    var post: ?[]const u8 = null;
    while (ast.tokens.items(.tag)[c.pos] == .doc_comment) : (c.pos += 1) {
        const comment = std.mem.trim(u8, c.text()[3..], " \t\r");
        if (std.mem.startsWith(u8, comment, "@ensures ")) {
            if (post != null) return error.UnsupportedContract;
            post = comment[9..];
        } else if (std.mem.indexOfScalar(u8, comment, '@') != null) return error.UnsupportedContract;
    }
    const formula = post orelse return error.MissingContract;
    try c.take("export");
    try c.take("fn");
    const function_name = try c.ident();
    try c.take("(");
    const input = try c.ident();
    if (std.mem.eql(u8, input, function_name)) return error.UnsupportedSource;
    try c.take(":");
    try c.take("u8");
    try c.take(")");
    try c.take("callconv");
    try c.take("(");
    try c.take(".");
    try c.take("c");
    try c.take(")");
    try c.take("u8");
    try c.take("{");
    try c.take("return");
    var body: Expr = undefined;
    if (std.mem.eql(u8, c.text(), input)) {
        c.pos += 1;
        if (std.mem.eql(u8, c.text(), "+%")) {
            c.pos += 1;
            body = .{ .add_wrap = try c.number() };
        } else body = .input;
    } else body = .{ .literal = try c.number() };
    try c.take(";");
    try c.take("}");
    if (ast.tokens.items(.tag)[c.pos] != .eof) return error.UnsupportedSource;

    var words = std.mem.tokenizeAny(u8, formula, " \t\r");
    for ([_][]const u8{ "result", "==", input, "+%" }) |want| {
        if (!std.mem.eql(u8, words.next() orelse return error.UnsupportedContract, want)) return error.UnsupportedContract;
    }
    const add = std.fmt.parseInt(u8, words.next() orelse return error.UnsupportedContract, 0) catch return error.UnsupportedContract;
    if (words.next() != null) return error.UnsupportedContract;
    var hash: [32]u8 = undefined;
    var hasher = std.crypto.hash.Blake3.init(.{});
    hasher.update("atoma.source.u8.v1\n");
    hasher.update(src);
    hasher.final(&hash);
    return .{ .body = body, .ensures_add = add, .source_hash = hash };
}

const good =
    \\/// @ensures result == x +% 1
    \\export fn increment(x: u8) callconv(.c) u8 { return x +% 1; }
;

test "source-derived u8 obligation includes overflow edge and source identity" {
    const p = try lower(std.testing.allocator, good);
    try std.testing.expectEqual(@as(?u8, null), p.counterexample());
    try std.testing.expectEqual(@as(u8, 0), p.body.eval(255));
    const q = try lower(std.testing.allocator, good ++ "\n// changed source\n");
    try std.testing.expect(!std.mem.eql(u8, &p.source_hash, &q.source_hash));
    var out = std.Io.Writer.Allocating.init(std.testing.allocator);
    defer out.deinit();
    try p.emit(&out.writer);
    try std.testing.expect(std.mem.indexOf(u8, out.written(), "(bvadd x (_ bv1 8))") != null);
}

test "wrong body with unchanged contract has a counterexample" {
    const bad =
        \\/// @ensures result == x +% 1
        \\export fn increment(x: u8) callconv(.c) u8 { return x +% 2; }
    ;
    const p = try lower(std.testing.allocator, bad);
    try std.testing.expectEqual(@as(?u8, 0), p.counterexample());
}

test "closed pilot rejects calls imports branching ordinary addition and contracts it cannot interpret" {
    const prefix = "/// @ensures result == x +% 1\nexport fn increment(x: u8) callconv(.c) u8 { ";
    for ([_][]const u8{
        prefix ++ "return increment(x); }",
        prefix ++ "return x + 1; }",
        prefix ++ "if (x == 0) return 1; return x; }",
        prefix ++ "return x +% 256; }",
        good ++ "\nconst other = @import(\"other.zig\");",
    }) |src| try std.testing.expectError(error.UnsupportedSource, lower(std.testing.allocator, src));
    try std.testing.expectError(error.MissingContract, lower(std.testing.allocator, "const hidden = @import(\"other.zig\");\n" ++ good));
    try std.testing.expectError(error.UnsupportedContract, lower(std.testing.allocator, "/// @requires true\n" ++ good));
    try std.testing.expectError(error.UnsupportedContract, lower(std.testing.allocator, "/// @ensures result == x +% 1\n" ++ good));
    try std.testing.expectError(error.UnsupportedSource, lower(std.testing.allocator, "/// @ensures result == _ +% 1\nexport fn f(_: u8) callconv(.c) u8 { return _; }"));
    try std.testing.expectError(error.UnsupportedSource, lower(std.testing.allocator, "/// @ensures result == x +% 1\nexport fn bool(x: u8) callconv(.c) u8 { return x; }"));
}
