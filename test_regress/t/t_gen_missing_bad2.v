// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   if ($test$plusargs("BAD-non-constant")) begin
      initial $stop;
   end
   case (1)
      $test$plusargs("BAD-non-constant"): initial $stop;
   endcase

endmodule
