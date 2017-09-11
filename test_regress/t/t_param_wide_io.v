// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Wilson Snyder.

// issue 1991

module t
  #(
    parameter[96:0] P = 97'h12344321_12344321_12344327
    )
   (
	input [P&7 - 1:0]  in,
	output [P&7 - 1:0] out
	);

   wire out = in;

endmodule
