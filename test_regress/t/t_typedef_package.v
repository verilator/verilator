// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Driss Hafdi.
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

module t (/*AUTOARG*/);
  initial begin
     $display("%d", pkg2::a);
     $write("*-* All Finished *-*\n");
     $finish;
  end
endmodule
