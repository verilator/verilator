// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [31:0] in_a;
   reg [31:0] in_b;

   reg [31:0] e,f,g,h;

   always @ (/*AS*/in_a) begin
      e = in_a;
      f = {e[15:0], e[31:16]};
      g = {f[15:0], f[31:16]};
      h = {g[15:0], g[31:16]};
   end

   // verilator lint_off UNOPTFLAT
   reg [31:0] e2,f2,g2,h2;
   always @ (/*AS*/f2, g2) begin
      h2 = {g2[15:0], g2[31:16]};
      g2 = {f2[15:0], f2[31:16]};
   end
   always @ (/*AS*/in_a, e2) begin
      f2 = {e2[15:0], e2[31:16]};
      e2 = in_a;
   end
   // verilator lint_on UNOPTFLAT

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         //$write("%d %x %x\n", cyc, h, h2);
         if (h != h2) $stop;
         if (cyc==1) begin
            in_a <= 32'h89a14fab;
            in_b <= 32'h7ab512fa;
         end
         if (cyc==2) begin
            in_a <= 32'hf4c11a42;
            in_b <= 32'h359967c6;
            if (h != 32'h4fab89a1) $stop;
         end
         if (cyc==3) begin
            if (h != 32'h1a42f4c1) $stop;
         end
         if (cyc==9) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end
endmodule
