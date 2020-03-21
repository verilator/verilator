// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Make sure type errors aren't suppressable
// verilator lint_off WIDTH

module t(/*AUTOARG*/);

   task checkset(const ref int bad_const_set);
      bad_const_set = 32'h4567;  // Bad setting const
   endtask

   task checkset2(ref int int_ref);
   endtask

   initial begin
      int i;
      byte bad_non_int;
      checkset(i);
      checkset2(bad_non_int);  // Type mismatch
   end
endmodule
