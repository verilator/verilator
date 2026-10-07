// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Only unused parameterized classes, no module

// False positive in t_dist_whitespace.py
// verilog_format: off

virtual class Cls #(
    parameter DECODE_W
);
endclass

class ClsDefault #(
    int P = 1
);
endclass
