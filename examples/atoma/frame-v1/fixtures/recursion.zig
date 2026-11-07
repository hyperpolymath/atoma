/// @contract atoma.audit.recursive
export fn recurse(value: u32) callconv(.c) u32 {
    return helper(value);
}

fn helper(value: u32) u32 {
    return recurse(value);
}
