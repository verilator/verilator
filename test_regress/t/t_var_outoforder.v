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
   integer cyc; initial cyc=1;

   reg [125:0] a;
   wire      q;

   sub sub (
            .q                          (q),
            .a                          (a),
            .clk                        (clk));

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            a <= 126'b1000;
         end
         if (cyc==2) begin
            a <= 126'h1001;
         end
         if (cyc==3) begin
            a <= 126'h1010;
         end
         if (cyc==4) begin
            a <= 126'h1111;
            if (q !== 1'b0) $stop;
         end
         if (cyc==5) begin
            if (q !== 1'b1) $stop;
         end
         if (cyc==6) begin
            if (q !== 1'b0) $stop;
         end
         if (cyc==7) begin
            if (q !== 1'b0) $stop;
         end
         if (cyc==8) begin
            if (q !== 1'b0) $stop;
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module sub (
   input clk,
   input [125:0] a,
   output reg q
   );

   // verilator public_module

   reg [125:0] g_r;

   wire [127:0] g_extend = { g_r, 1'b1, 1'b0 };

   reg [6:0] sel;
   wire      g_sel = g_extend[sel];

   always @ (posedge clk) begin
      g_r <= a;
      sel <= a[6:0];
      q <= g_sel;
   end

endmodule
