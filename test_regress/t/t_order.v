// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   // surefire lint_off ASWEBB
   // surefire lint_off ASWEMB
   // surefire lint_off STMINI
   // surefire lint_off CSEBEQ

   input clk;

   reg [7:0] a_to_clk_levm3;
   reg [7:0] b_to_clk_levm1;
   reg [7:0] c_com_levs10;
   reg [7:0] d_to_clk_levm2;
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]           m_from_clk_lev1_r;      // From a of t_order_a.v
   wire [7:0]           n_from_clk_lev2;        // From a of t_order_a.v
   wire [7:0]           o_from_com_levs11;      // From a of t_order_a.v
   wire [7:0]           o_from_comandclk_levs12;// From a of t_order_a.v
   wire [7:0]           o_subfrom_clk_lev2;     // From b of t_order_b.v
   // End of automatics

   reg [7:0] cyc; initial cyc = 0;

   t_order_a a (
                .one                    (8'h1),
                /*AUTOINST*/
                // Outputs
                .m_from_clk_lev1_r      (m_from_clk_lev1_r[7:0]),
                .n_from_clk_lev2        (n_from_clk_lev2[7:0]),
                .o_from_com_levs11      (o_from_com_levs11[7:0]),
                .o_from_comandclk_levs12(o_from_comandclk_levs12[7:0]),
                // Inputs
                .clk                    (clk),
                .a_to_clk_levm3         (a_to_clk_levm3[7:0]),
                .b_to_clk_levm1         (b_to_clk_levm1[7:0]),
                .c_com_levs10           (c_com_levs10[7:0]),
                .d_to_clk_levm2         (d_to_clk_levm2[7:0]));

   t_order_b b (
                /*AUTOINST*/
                // Outputs
                .o_subfrom_clk_lev2     (o_subfrom_clk_lev2[7:0]),
                // Inputs
                .m_from_clk_lev1_r      (m_from_clk_lev1_r[7:0]));

   reg [7:0]  o_from_com_levs12;
   reg [7:0]  o_from_com_levs13;
   always @ (/*AS*/o_from_com_levs11) begin
      o_from_com_levs12 = o_from_com_levs11 + 8'h1;
      o_from_com_levs12 = o_from_com_levs12 + 8'h1;  // Test we can add to self and optimize
      o_from_com_levs13 = o_from_com_levs12;
   end

   reg          sepassign_in;
   // verilator lint_off UNOPTFLAT
   wire [3:0]   sepassign;
   // verilator lint_on UNOPTFLAT

   // verilator lint_off UNOPT
   assign #0.1  sepassign[0]    = 0,
                sepassign[1]    = sepassign[2],
                sepassign[2]    = sepassign[3],
                sepassign[3]    = sepassign_in;
   wire [7:0]   o_subfrom_clk_lev3 = o_subfrom_clk_lev2;
   // verilator lint_on UNOPT

   always @ (posedge clk) begin
      cyc <= cyc+8'd1;
      sepassign_in <= 0;
      if (cyc == 8'd1) begin
         a_to_clk_levm3 <= 0;
         d_to_clk_levm2 <= 1;
         b_to_clk_levm1 <= 1;
         c_com_levs10 <= 2;
         sepassign_in <= 1;
      end
      if (cyc == 8'd2) begin
         if (sepassign !== 4'b1110) $stop;
      end
      if (cyc == 8'd3) begin

         $display("%d %d %d %d", m_from_clk_lev1_r,
                  n_from_clk_lev2,
                  o_from_com_levs11,
                  o_from_comandclk_levs12);

         if (m_from_clk_lev1_r !== 8'h2) $stop;
         if (o_subfrom_clk_lev3 !== 8'h2) $stop;
         if (n_from_clk_lev2 !== 8'h2) $stop;
         if (o_from_com_levs11 !== 8'h3) $stop;
         if (o_from_com_levs13 !== 8'h5) $stop;
         if (o_from_comandclk_levs12 !== 8'h5) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
