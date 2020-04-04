// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   string s;
   integer i;

   // Check constification
   initial begin
      s="1234";
      i = s.len(0); // BAD
      s.itoa;  // BAD
      s.itoa(1,2,3);  // BAD
   end

endmodule
