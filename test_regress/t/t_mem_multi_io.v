// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic [7:0] arr [7:0];
   logic [7:0] arri [7:0];

   has_array am1 (.clk(clk), .arri(arr), .arro(arri));

   integer cyc; initial cyc = 0;

   initial begin
      for (int i = 0; i < 8; i++) begin
	  arr[i] = 0;
      end
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 5 && arri[1] != 8) begin
         $stop;
      end
      for (int i = 0; i < 7; ++i) begin
	  arr[i+1] <= arr[i];
      end
      arr[0] <= arr[0] + 1;
   end

endmodule : t

module has_array (
   input clk,
   input logic [7:0] arri [7:0],
   output logic [7:0] arro [7:0]
   );

   integer cyc; initial cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (arri[0] == 10 && cyc == 10) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   always @(posedge clk) begin
      for (integer i = 0; i < 7; ++i) begin
	  arro[i+1] <= arro[i];
      end
      arro[0] = arro[0] + 2;
   end

endmodule : has_array
