// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Yossi Nivin.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [15:0] in16;
   reg [31:0] in32;
   reg [63:0] in64;
   // Non-standard size
   reg [9:0] in10;
   reg [20:0] in21;
   reg [58:0] in59;
   reg [69:0] in70;

   reg [31:0] ctrl0;
   reg [31:0] ctrl1;
   reg [31:0] ctrl2;

   reg [4:0] result_16_1;
   reg [4:0] result_16_2;
   reg [4:0] result_16_3;
   reg [5:0] result_32_1;
   reg [5:0] result_32_2;
   reg [5:0] result_32_3;
   reg [6:0] result_64_1;
   reg [6:0] result_64_2;
   reg [6:0] result_64_3;
   reg [3:0] result_10_3;
   reg [4:0] result_21_3;
   reg [5:0] result_59_3;
   reg [6:0] result_70_3;

   initial begin
      if ($countbits(32'b111100000000, '1) != 4) $stop;
      if ($countbits(32'b111100000000, '0) != 28) $stop;
      if ($countbits(32'b111100000000, '0, '1) != 32) $stop;
      if ($countbits(4'bxxx0, 'x) != 3) $stop;
      if ($countbits(4'bzzz0, 'z) != 3) $stop;
      if ($countbits(4'b1zz0, 'z, '0) != 3) $stop;
      if ($countbits(4'b1xx0, 'x, '0) != 3) $stop;
      if ($countbits(4'b1xx0, 'x, '0, '1) != 4) $stop;
      if ($countbits(4'bzzx0, 'x, 'z) != 3) $stop;
   end

   always @* begin
      result_16_1 = $countbits(in16, ctrl0);
      result_16_2 = $countbits(in16, ctrl0, ctrl1);
      result_16_3 = $countbits(in16, ctrl0, ctrl1, ctrl2);

      result_32_1 = $countbits(in32, ctrl0);
      result_32_2 = $countbits(in32, ctrl0, ctrl1);
      result_32_3 = $countbits(in32, ctrl0, ctrl1, ctrl2);

      result_64_1 = $countbits(in64, ctrl0);
      result_64_2 = $countbits(in64, ctrl0, ctrl1);
      result_64_3 = $countbits(in64, ctrl0, ctrl1, ctrl2);

      result_10_3 = $countbits(in10, ctrl0, ctrl1, ctrl2);
      result_21_3 = $countbits(in21, ctrl0, ctrl1, ctrl2);
      result_59_3 = $countbits(in59, ctrl0, ctrl1, ctrl2);
      result_70_3 = $countbits(in70, ctrl0, ctrl1, ctrl2);
   end

   logic [31:0] val = 32'h70008421;

   integer cyc = 0;
   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         // Constants
         if ($countbits(32'b11001011101, '1) != 7) $stop;
         if ($countbits(32'b11001011101, '1, 'z) != 7) $stop;
         if ($countbits(32'b11001011101, '1, '0) != 32) $stop;
         if ($countbits(20'b11001011101, '1, '0) != 20) $stop;
         if ($countbits(20'b1100x01z101, '1, '0) != 18) $stop;
         if ($countbits(20'b1100x01z101, 2, 2'bx1) != 18) $stop;
         if ($countbits(32'b1100x01z101, 'x, 'z) != 2) $stop;
         if ($countbits(32'b1100x01z101, 'x, 'z, '1) != 7) $stop;

         if ($countbits(val, '1) != 7) $stop;
         if ($countones(val) != 7) $stop;
         if ($countbits(val, '0) != 25) $stop;
         if ($countbits(val, '0, '1) != 32) $stop;
         // Optimization may depend on position of X, so need to walk it
         if ($countbits(val, 'x) != 0) $stop;
         if ($countbits(val, 'x, '1) != 7) $stop;
         if ($countbits(val, '1, 'x) != 7) $stop;
         if ($countbits(val, '1, '1, 'x) != 7) $stop;
         if ($countbits(val, 'x, '0) != 25) $stop;
         if ($countbits(val, 'x, '0, '1) != 32) $stop;
         // Optimization may depend on position of Z, so need to walk it
         if ($countbits(val, 'z) != 0) $stop;
         if ($countbits(val, 'z, '1) != 7) $stop;
         if ($countbits(val, '1, 'z) != 7) $stop;
         if ($countbits(val, '1, '1, 'z) != 7) $stop;
         if ($countbits(val, 'z, '0) != 25) $stop;
         if ($countbits(val, 'z, '0, '1) != 32) $stop;
         //
         if ($countbits(val, 'x, 'z) != 0) $stop;
      end
      else if (cyc == 1) begin
         in16 <= 16'h0AF0;
         in32 <= 32'hA0F300;
         in64 <= 64'hA5A5A5A5A5A5A5A5;
         in10 <= 10'b1010_1011;
         in21 <= 21'h10F102;
         in59 <= 59'h7050137210;
         in70 <= 70'hF00030008000;
         ctrl0 <= '0;
         ctrl1 <= '1;
         ctrl2 <= '1;
      end
      else if (cyc == 2) begin
         if (result_16_1 != 10) $stop;
         if (result_16_2 != 16) $stop;
         if (result_16_3 != 16) $stop;
         if (result_32_1 != 24) $stop;
         if (result_32_2 != 32) $stop;
         if (result_32_3 != 32) $stop;
         if (result_64_1 != 32) $stop;
         if (result_64_2 != 64) $stop;
         if (result_64_3 != 64) $stop;
         if (result_10_3 != 10) $stop;
         if (result_21_3 != 21) $stop;
         if (result_59_3 != 59) $stop;
         if (result_70_3 != 70) $stop;

         in16 <= 16'h82B;
         in32 <= 32'h305372;
         in64 <= 64'h7777777777777777;
         in10 <= 10'b1001_0111;
         in21 <= 21'h91040C;
         in59 <= 59'h12345678;
         in70 <= 70'hF11111111;
         // Confirm upper bits of the control arguments are ignored
         ctrl0 <= 5;
         ctrl1 <= 3;
         ctrl2 <= 2;
      end
      else if (cyc == 3) begin
         if (result_16_1 != 5) $stop;
         if (result_16_2 != 5) $stop;
         if (result_16_3 != 16) $stop;
         if (result_32_1 != 10) $stop;
         if (result_32_2 != 10) $stop;
         if (result_32_3 != 32) $stop;
         if (result_64_1 != 48) $stop;
         if (result_64_2 != 48) $stop;
         if (result_64_3 != 64) $stop;
         if (result_10_3 != 10) $stop;
         if (result_21_3 != 21) $stop;
         if (result_59_3 != 59) $stop;
         if (result_70_3 != 70) $stop;
      end
      else if (cyc == 4) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
