// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire [3:0] a = 4'b10z0;
   logic     b = 2'bzz === 2'(a[1]);
   logic     c = 2'b0z === 2'(a[1]);

   always begin
      if (!b && c) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Error: b = %b, c = %b, ", b, c);
         $write("expected: b = 0, c = 1\n");
         $stop;
      end
   end
endmodule
