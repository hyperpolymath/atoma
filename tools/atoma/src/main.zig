// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// atoma — content addressing and canonicalisation for Atoma.
//
// This is a convenience tool, NOT part of the trusted computing base. The
// authoritative encoder is `encode` in src/atoma/spec/CoreSpec.idr.
//
// Usage:
//   atoma canon   <file.cspec>        print the canonical bytes
//   atoma hash    <file.cspec>        print blake3:<hex> of the spec
//   atoma dk-hash <file.dk>           print blake3:<hex> of a witness
//   atoma src-hash <file>             print blake3:<hex> of proof source
//   atoma equiv   <a.cspec> <b.cspec> exit 0 iff the faces agree
//   atoma mutate  <file.cspec> <op>   print one mutated specification
//   atoma extract <file.zig> [--symbol S]     emit the Face B contract (.cspec)
//   atoma check   <file.zig>                  subset conformance, exit 1 on E-*
//   atoma vc      <outdir>                    emit the 14 SMT-LIB queries + manifest
//   atoma ops                         list mutation operators
//   atoma selftest                    run the built-in vectors
//
// Exit codes: 0 success/agree, 1 disagreement or verification failure,
//             2 usage error, 3 I/O or parse error.

const std = @import("std");
const canon = @import("canon.zig");
const frontend = @import("frontend.zig");
const vc = @import("vc.zig");

const gpa = std.heap.page_allocator;

fn readFile(path: []const u8) ![]u8 {
    return std.fs.cwd().readFileAlloc(gpa, path, 16 << 20);
}

fn writeFile(path: []const u8, bytes: []const u8) !void {
    const f = try std.fs.cwd().createFile(path, .{});
    defer f.close();
    try f.writeAll(bytes);
}

/// Results go to stdout; diagnostics go to stderr. Both are best-effort: a
/// closed pipe is not an error worth a panic in a build tool.
fn say(bytes: []const u8) void {
    std.fs.File.stdout().writeAll(bytes) catch {};
}

fn sayLine(bytes: []const u8) void {
    say(bytes);
    say("\n");
}

fn print(comptime fmt: []const u8, args: anytype) void {
    var buf: [4096]u8 = undefined;
    const s = std.fmt.bufPrint(&buf, fmt, args) catch return;
    say(s);
}

fn usage() noreturn {
    sayLine("usage: atoma <canon|hash|vc-hash|dk-hash|src-hash|extract|check|vc|equiv|mutate|ops|selftest> [args]");
    std.process.exit(2);
}

pub fn main() !void {
    // PINNED to Zig 0.15.2: `std.process.argsAlloc` exists there and was removed
    // by 0.16/0.17 (args become a value passed to main). See §5.2 of the spec:
    // this one line is the whole 0.15 -> 0.16 port, and it is exactly the kind of
    // churn the hybrid frontend is designed to absorb.
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    if (args.len < 2) usage();
    const cmd = args[1];

    if (std.mem.eql(u8, cmd, "canon")) {
        if (args.len != 3) usage();
        const src = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const c = canon.canon(gpa, src) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        say(c.bytes);
    } else if (std.mem.eql(u8, cmd, "hash")) {
        if (args.len != 3) usage();
        const src = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const c = canon.canon(gpa, src) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const hx = c.hex();
        print("blake3:{s}\n", .{hx});
    } else if (std.mem.eql(u8, cmd, "dk-hash")) {
        if (args.len != 3) usage();
        const bytes = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const hx = canon.digestHex(canon.domain_dk, bytes);
        print("blake3:{s}\n", .{hx});
    } else if (std.mem.eql(u8, cmd, "src-hash")) {
        if (args.len != 3) usage();
        const bytes = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const hx = canon.digestHex(canon.domain_src, bytes);
        print("blake3:{s}\n", .{hx});
    } else if (std.mem.eql(u8, cmd, "vc-hash")) {
        if (args.len != 3) usage();
        const bytes = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const hx = canon.digestHex(canon.domain_vc, bytes);
        print("blake3:{s}\n", .{hx});
    } else if (std.mem.eql(u8, cmd, "equiv")) {
        if (args.len != 4) usage();
        const a_src = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const b_src = readFile(args[3]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const a = canon.canon(gpa, a_src) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const b = canon.canon(gpa, b_src) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const ah = a.hex();
        const bh = b.hex();
        if (std.mem.eql(u8, &ah, &bh)) {
            print("EQUIVALENT blake3:{s}\n", .{ah});
        } else {
            print("DIVERGENT\n  face-a blake3:{s}\n  face-b blake3:{s}\n", .{ ah, bh });
            std.process.exit(1);
        }
    } else if (std.mem.eql(u8, cmd, "mutate")) {
        if (args.len != 4) usage();
        const src = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        const m = std.meta.stringToEnum(canon.Mutation, args[3]) orelse {
            sayLine("unknown mutation operator; try `atoma ops`");
            std.process.exit(2);
        };
        const out = canon.applyMutation(gpa, src, m) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        if (out) |bytes| {
            say(bytes);
        } else {
            print("NOT-APPLICABLE {s}\n", .{m.name()});
            std.process.exit(1);
        }
    } else if (std.mem.eql(u8, cmd, "extract")) {
        if (args.len < 3) usage();
        const src = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        var symbol: []const u8 = "";
        var i: usize = 3;
        while (i + 1 < args.len) : (i += 2) {
            if (std.mem.eql(u8, args[i], "--symbol")) symbol = args[i + 1];
        }
        const base = std.fs.path.stem(args[2]);
        const out = frontend.extract(gpa, src, .{ .symbol = symbol, .default_name = base }) catch |e| {
            print("extract failed: {s}\n", .{@errorName(e)});
            std.process.exit(1);
        };
        say(out);
    } else if (std.mem.eql(u8, cmd, "check")) {
        if (args.len < 3) usage();
        const src = readFile(args[2]) catch |e| {
            sayLine(@errorName(e));
            std.process.exit(3);
        };
        var rep = frontend.check(gpa, src, .{}) catch |e| {
            print("check failed: {s}\n", .{@errorName(e)});
            std.process.exit(3);
        };
        defer rep.deinit(gpa);
        for (rep.diags.items) |d| {
            print("{s}:{d}: {s}: {s}\n", .{ args[2], d.line, d.code, d.detail });
        }
        print("{s}: {d} declarations, {d} exports, {d} contracts, {d} diagnostics\n", .{
            args[2], rep.decls, rep.exports, rep.contracts, rep.diags.items.len,
        });
        if (rep.diags.items.len != 0) std.process.exit(1);
    } else if (std.mem.eql(u8, cmd, "vc")) {
        if (args.len < 3) usage();
        var cspec: ?[]const u8 = null;
        var i: usize = 3;
        while (i + 1 < args.len) : (i += 2) {
            if (std.mem.eql(u8, args[i], "--cspec")) cspec = args[i + 1];
        }
        if (cspec) |path| {
            const src = readFile(path) catch |e| {
                print("cannot read {s}: {s}\n", .{ path, @errorName(e) });
                std.process.exit(3);
            };
            const c = canon.canon(gpa, src) catch |e| {
                print("cannot canonicalise {s}: {s}\n", .{ path, @errorName(e) });
                std.process.exit(3);
            };
            vc.checkContract(c.bytes) catch {
                print("CONTRACT-DRIFT {s}: the query set is pinned to a contract that changed\n", .{path});
                sayLine("  re-derive the obligations in docs/spec/ATOMA-SPEC.adoc §8.3 before regenerating");
                std.process.exit(1);
            };
        }
        var dir = std.fs.cwd().openDir(args[2], .{}) catch |e| {
            print("cannot open {s}: {s}\n", .{ args[2], @errorName(e) });
            std.process.exit(3);
        };
        defer dir.close();
        _ = vc.generate(gpa, dir) catch |e| {
            print("vc generation failed: {s}\n", .{@errorName(e)});
            std.process.exit(3);
        };
        // The manifest is the reviewed expectation table, emitted from the same
        // source of truth as the queries. `verify.sh` diffs it against the
        // checked-in `vc/expected.tsv`, so a changed expectation is a reviewed
        // diff rather than a silent edit to the generator.
        var buf = std.io.Writer.Allocating.init(gpa);
        defer buf.deinit();
        vc.writeManifest(&buf.writer) catch |e| {
            print("cannot render manifest: {s}\n", .{@errorName(e)});
            std.process.exit(3);
        };
        var mf = dir.createFile("manifest.tsv", .{}) catch |e| {
            print("cannot write manifest: {s}\n", .{@errorName(e)});
            std.process.exit(3);
        };
        defer mf.close();
        mf.writeAll(buf.written()) catch |e| {
            print("cannot write manifest: {s}\n", .{@errorName(e)});
            std.process.exit(3);
        };
        print("{d} VCs -> {s}\n", .{ vc.vcs.len, args[2] });
    } else if (std.mem.eql(u8, cmd, "ops")) {
        for (canon.Mutation.all()) |m| print("{s}\n", .{m.name()});
    } else if (std.mem.eql(u8, cmd, "selftest")) {
        // Two syntactically different faces of the same contract must collide;
        // a one-token difference must not.
        const face_a =
            \\# Face A: extracted from Idris2 (ghost params elided)
            \\cspec 1
            \\contract demo.frame.parse
            \\kind extern
            \\param h 1 handle
            \\param in 0 slice ro u8 r0
            \\param out 1 ptr out_frame r1
            \\requires ( <= ( len in ) 65535 )
            \\ensures ( <= ( + ( len in ) 0 ) 65535 )
            \\cap Alloc
            \\
        ;
        const face_b =
            \\# Face B: inline Zig contract, written by a different author
            \\cspec 1
            \\contract demo.frame.parse
            \\kind extern
            \\param h 1 handle
            \\param in 0 slice ro u8 r0
            \\param out 1 ptr out_frame r1
            \\requires ( <= ( len in ) 0xffff )
            \\ensures ( <= ( + ( len in ) 000 ) 65535 )
            \\cap Alloc
            \\
        ;
        const a = try canon.canon(gpa, face_a);
        const b = try canon.canon(gpa, face_b);
        const ah = a.hex();
        const bh = b.hex();
        if (!std.mem.eql(u8, &ah, &bh)) {
            print("selftest FAIL (faces should agree)\n  a=blake3:{s}\n  b=blake3:{s}\n", .{ ah, bh });
            std.process.exit(1);
        }
        const broken = try canon.canon(gpa, face_b ++ "requires ( < ( len in ) 65535 )\n");
        const ch = broken.hex();
        if (std.mem.eql(u8, &ah, &ch)) {
            sayLine("selftest FAIL (weakened face did not diverge)");
            std.process.exit(1);
        }
        print("selftest OK\n  agreement blake3:{s}\n  divergence blake3:{s}\n", .{ ah, ch });
    } else {
        usage();
    }
}

test {
    _ = canon;
    _ = vc;
}
