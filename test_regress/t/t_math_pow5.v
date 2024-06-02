// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [67:0] q;
   reg signed [67:0] qs;

   initial begin
      q = 68'he_12345678_9abcdef0 ** 68'h3;
      if (q != 68'hcee3cb96ce96cf000) $stop;
      //
      q = 68'he_12345678_9abcdef0 ** 68'h5_6789abcd_ef012345;
      if (q != 68'h0) $stop;
      //
      qs = 68'she_12345678_9abcdef0 ** 68'sh3;
      if (qs != 68'shcee3cb96ce96cf000) $stop;
      //
      qs = 68'she_12345678_9abcdef0 ** 68'sh5_6789abcd_ef012345;
      if (qs != 68'h0) $stop;
   end

   reg [67:0] left;
   reg [67:0] right;

   wire [67:0] outu = left ** right;
   wire signed [67:0] outs = $signed(left) ** $signed(right);

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
`ifdef TEST_VERBOSE
         $write("%d %x %x %x %x\n", cyc, left, right, outu, outs);
`endif
         if (cyc==1) begin
            left <= 68'h1;
            right <= '0;
         end
         if (cyc==2) begin
            if (outu  != 68'h1) $stop;
            if (outs  != 68'h1) $stop;
         end
         if (cyc==3) begin
            left <= 68'he_12345678_9abcdef0;
            right <= 68'h3;
         end
         if (cyc==4) begin
            if (outu != 68'hcee3cb96ce96cf000) $stop;
            if (outs != 68'hcee3cb96ce96cf000) $stop;
         end
         if (cyc==5) begin
            left <= 68'he_12345678_9abcdef0;
            right <= 68'h5_6789abcd_ef012345;
         end
         if (cyc==6) begin
            if (outu != 68'h0) $stop;
            if (outs != 68'h0) $stop;
         end
         if (cyc==9) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end
endmodule
