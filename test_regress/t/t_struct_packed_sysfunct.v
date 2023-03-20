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
   } struct_dsc;  // descendng range structure
   /* verilator lint_off ASCRANGE */
   struct packed {
      logic       e0;
      logic [0:1] e1;
      logic [0:3] e2;
      logic [0:7] e3;
   } struct_asc;  // ascending range structure
   /* verilator lint_on ASCRANGE */

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
      // descending range
      if ($bits (struct_dsc   ) != 15) $stop;
      if ($bits (struct_dsc.e0) !=  1) $stop;
      if ($bits (struct_dsc.e1) !=  2) $stop;
      if ($bits (struct_dsc.e2) !=  4) $stop;
      if ($bits (struct_dsc.e3) !=  8) $stop;
      if ($increment (struct_dsc, 1) !=  1) $stop;
      // ascending range
      if ($bits (struct_asc   ) != 15) $stop;
      if ($bits (struct_asc.e0) !=  1) $stop;
      if ($bits (struct_asc.e1) !=  2) $stop;
      if ($bits (struct_asc.e2) !=  4) $stop;
      if ($bits (struct_asc.e3) !=  8) $stop;
      if ($increment (struct_asc, 1) != 1) $stop;  // Structure itself always big numbered
   end

endmodule
