// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug475

module t();

   function real get_real_one;
      input           ignored;
      get_real_one = 1.1;
   endfunction

   localparam R_PARAM = get_real_one(1'b0);
   localparam R_PARAM_2 = (R_PARAM > 0);

   generate
      initial begin
         if (R_PARAM != 1.1) $stop;
         if (R_PARAM_2 != 1'b1) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   endgenerate

endmodule
