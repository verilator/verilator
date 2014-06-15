// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

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
    output [63:0] 	s1,
    output [63:0] 	s2
);
   initial struct1 = 64'h123456789_abcdef0;
   always_comb s1 = struct1;
   initial struct2 = 64'h123456789_abcdef0;
   always_comb s2 = struct2;
endmodule

