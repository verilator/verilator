// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;
   typedef struct packed {
      logic [3:0] msk;
      logic [3:0] dat;
   } STR_t;
endpackage;

package csr_pkg;
   typedef pkg::STR_t reg_t;
   localparam reg_t REG_RST = 8'h34;
endpackage

module t;
   initial begin
      if (csr_pkg::REG_RST.msk != 4'h3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
