// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire [3:0] a = 4'b11z1;
   logic     b = 1'bz === a[1];
   logic     c = 1'bz === a[2];
   logic     d = 2'bzz === 2'(a[1]);
   logic     e = 2'b0z === 2'(a[1]);


   always begin
      if (b && !c && !d && e) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Error: b = %b, c = %b, d = %b, e = %b ", b, c, d, e);
         $write("expected: b = 1, c = 0, d = 0, e = 1\n");
         $stop;
      end
   end
endmodule
