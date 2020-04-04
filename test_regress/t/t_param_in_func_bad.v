// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Driss Hafdi.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic [7:0] digit = getDigit(4'd1);

   initial begin
      if (digit != "1") $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

function automatic logic[7:0] getDigit(logic[3:0] d);
   localparam logic[7:0] digits[10]
                         = '{
                             "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"
                             };
   return digits[d];
endfunction
