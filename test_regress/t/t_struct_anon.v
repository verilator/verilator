// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Anonymous
struct packed {
    logic [31:0] val1;
    logic [31:0] val2;
} struct1;

struct packed {
    logic [31:0] val3;
    logic [31:0] val4;
} struct2;

module t (
    output logic [63:0] s1,
    output logic [63:0] s2
);
   initial struct1 = 64'h123456789_abcdef0;
   always_comb s1 = struct1;
   initial struct2 = 64'h123456789_abcdef0;
   always_comb s2 = struct2;
endmodule
