// DESCRIPTION: Verilator: Verilog Test module
//
// This files is used to generated the BLKLOOPINIT error which
// is actually caused by not being able to unroll the for loop.
//
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Jie Xu.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg    [3:0] tmp [3:0];

   initial begin
      tmp[0] = 4'b0000;
      tmp[2] = 4'b0010;
      tmp[3] = 4'b0011;
   end

   // Test loop
   always @ (posedge clk) begin
      int i;
      int j;
      for (i = 0;(i < 4) && (i > 1); i++) begin
         tmp[i] <= tmp[i-i];
      end
      if (tmp[0] != 4'b0000) $stop;
      if (tmp[3] != 4'b0011) $stop;

      j = 0; for (i=$c32("1"); i<3; ++i) j++;
      if (j!=2) $stop;
      j = 0; for (i=1; i<$c32("3"); ++i) j++;
      if (j!=2) $stop;
      j = 0; for (i=1; i<3; i=i+$c32("1")) j++;
      if (j!=2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
