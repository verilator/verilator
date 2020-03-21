// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off UNDRIVEN

module t();
   wire sig;
   sub sub0(.out(33'b0));
   sub sub1(.out({32'b0, sig}));
   sub sub2(.out({32'b1, sig}));
endmodule

module sub(output reg [32 : 0] out);
endmodule
