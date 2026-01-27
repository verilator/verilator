// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2011 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

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
