// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // packed structures
   struct packed {
      logic       e0;
      logic [1:0] e1;
      logic [3:0] e2;
      logic [7:0] e3;
   } struct_bg;  // big endian structure
   /* verilator lint_off LITENDIAN */
   struct packed {
      logic       e0;
      logic [0:1] e1;
      logic [0:3] e2;
      logic [0:7] e3;
   } struct_lt;  // little endian structure
   /* verilator lint_on LITENDIAN */

   integer cnt = 0;

   // event counter
   always @ (posedge clk)
   begin
      cnt <= cnt + 1;
   end

   // finish report
   always @ (posedge clk)
   if (cnt==2) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   always @ (posedge clk)
   if (cnt==1) begin
      // big endian
      if ($bits (struct_bg   ) != 15) $stop;
      if ($bits (struct_bg.e0) !=  1) $stop;
      if ($bits (struct_bg.e1) !=  2) $stop;
      if ($bits (struct_bg.e2) !=  4) $stop;
      if ($bits (struct_bg.e3) !=  8) $stop;
      if ($increment (struct_bg, 1) !=  1) $stop;
      // little endian
      if ($bits (struct_lt   ) != 15) $stop;
      if ($bits (struct_lt.e0) !=  1) $stop;
      if ($bits (struct_lt.e1) !=  2) $stop;
      if ($bits (struct_lt.e2) !=  4) $stop;
      if ($bits (struct_lt.e3) !=  8) $stop;
      if ($increment (struct_lt, 1) != 1) $stop;  // Structure itself always big numbered
   end

endmodule
