// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
pub fn known(tag: u8) bool {
    return tag >= 1 and tag <= 9;
}
