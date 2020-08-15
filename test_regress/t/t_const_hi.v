// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   reg [1:0] reg_i;
   reg [1049:0] pad0;
   reg [1049:0] reg_o;
   reg [1049:0] spad1;

   /*AUTOWIRE*/

   always_comb begin
      if (reg_i[1] == 1'b1)
        reg_o = {986'd0, 64'hffff0000ffff0000};
      else if (reg_i[0] == 1'b1)
        reg_o = {64'hffff0000ffff0000, 986'd0};
      else
        reg_o = 1050'd0;
   end

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         reg_i <= 2'b00;
         pad0 <= '1;
         spad1 <= '1;
      end
      else if (cyc == 1) begin
         reg_i <= 2'b01;
      end
      else if (cyc == 2) begin
         if (reg_o != {64'hffff0000ffff0000, 986'd0}) $stop;
         reg_i <= 2'b10;
      end
      else if (cyc == 99) begin
         if (reg_o != {986'd0, 64'hffff0000ffff0000}) $stop;
         if (pad0 != '1) $stop;
         if (spad1 != '1) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
