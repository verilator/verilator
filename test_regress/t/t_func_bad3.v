// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   function recurse_self;
      input i;
      if (i == 0) recurse_self = 0;
      else recurse_self = recurse_self(i - 1) + 1;
   endfunction

endmodule
