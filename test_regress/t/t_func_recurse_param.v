// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   function automatic int recurse_self;
      input int i;
      if (i == 0) recurse_self = 0;
      else recurse_self = i + recurse_self(i - 1) * 2;
   endfunction

   localparam int ZERO = recurse_self(0);
   localparam int ELEVEN = recurse_self(3);

   initial begin
      if (ZERO != 0) $stop;
      if (ELEVEN != 11) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
