// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire signed [16:0] fft_oQ [6:0];
   round round(
               .i_data(fft_oQ[6:0])
               );
endmodule
module round(
             input wire signed [16:0] i_data  // Misdeclared, not a vector
             );
   wire signed [15:0] w_convergent = {10'b0, {6{~i_data[7]}}};
endmodule
