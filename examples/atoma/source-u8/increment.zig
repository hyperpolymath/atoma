/// @ensures result == x +% 1
export fn increment(x: u8) callconv(.c) u8 {
    return x +% 1;
}
