// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2016 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t
   (
   input wire rst
   );

   integer q;

   // verilator lint_off LATCH
   always @(*)
     if (rst)
       assign q = 0;
     else
       deassign q;
   // verilator lint_on LATCH

endmodule
