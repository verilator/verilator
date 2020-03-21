// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
   (
   input wire rst
   );

   integer q;

   always @(*)
     if (rst)
       assign q = 0;
     else
       deassign q;

endmodule
