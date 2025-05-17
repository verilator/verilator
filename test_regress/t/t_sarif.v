// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(
    input clk1,
    input clk2,
    output logic multidriven);

   wire [1:0] trunced = 5'b11111;  // Warned

   always @ (posedge clk1)
     multidriven <= '1;
   always @ (posedge clk2)
     multidriven <= '0;

endmodule

module t;  // BAD duplicate
endmodule
