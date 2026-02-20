// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   parameter P = 4'h5;

   struct packed {
      bit [3:0] m_lo = P;  // Bad
      bit [3:0] m_hi;
   } s;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
