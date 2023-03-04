// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   parameter P = 4'h5;

   struct {  // Can't legally be packed
      bit [3:0] m_lo = P;
      bit [3:0] m_hi;
   } s;

   initial begin
      s.m_hi = 4'ha;
      if (s.m_lo != 4'h5) $stop;
      if (s.m_hi != 4'ha) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
