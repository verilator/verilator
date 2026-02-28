// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Driss Hafdi
// SPDX-License-Identifier: CC0-1.0

package pkg1;
   typedef logic [7:0] uint8_t;
endpackage

package pkg2;
   typedef enum pkg1::uint8_t {
      a = 8'd1,
      b = 8'd2
   } opts;
endpackage

module t;
  initial begin
     $display("%d", pkg2::a);
     $write("*-* All Finished *-*\n");
     $finish;
  end
endmodule
