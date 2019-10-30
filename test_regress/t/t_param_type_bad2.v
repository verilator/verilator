// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t;
   localparam t = logic;  // Bad
   localparam t2 = realtime;  // Bad
endmodule
