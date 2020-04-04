// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   initial begin
      // verilator lint_off IGNOREDRETURN
      func(0, 1'b1);
   end

   function automatic int func
     (
      input int a,
      output bit b );
      return 0;
   endfunction

endmodule
