// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t;
   localparam type t = logic;  // Fine
   localparam type bad2 = 2;  // Bad
endmodule
