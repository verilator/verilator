// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

function int zeroed;
endfunction

function automatic integer what_bit;
   input [31:0] a;
   // what_bit = 0;
   for (int i = 31; i >= 0; i = i - 1) begin
      if (a[i] == 1'b1) begin
         what_bit = i;
      end
   end
endfunction

module t(/*AUTOARG*/);

   parameter ZERO = zeroed();

   parameter PP = what_bit(0);

   initial begin
      if (ZERO != 0) $stop;
      if (PP != 'x) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
