// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module secret #(parameter GATED_CLK = 0)
   (
    input [31:0]              accum_in,
    output wire [31:0]        accum_out,
    input                     accum_bypass,
    output [31:0]             accum_bypass_out,
    input                     s1_in,
    output logic              s1_out,
    input                     s1up_in[2],
    output logic              s1up_out[2],
    input [1:0]               s2_in,
    output logic [1:0]        s2_out,
    input [7:0]               s8_in,
    output logic [7:0]        s8_out,
    input [32:0]              s33_in,
    output logic [32:0]       s33_out,
    input [63:0]              s64_in,
    output logic [63:0]       s64_out,
    input [64:0]              s65_in,
    output logic [64:0]       s65_out,
    input [128:0]             s129_in,
    output logic [128:0]      s129_out,
    input [3:0] [31:0]        s4x32_in,
    output logic [3:0] [31:0] s4x32_out,
    /*verilator lint_off LITENDIAN*/
    input [0:15]              s6x16up_in[0:1][2:0],
    output logic [0:15]       s6x16up_out[0:1][2:0],
    /*verilator lint_on LITENDIAN*/
    input [15:0]              s8x16up_in[1:0][0:3],
    output logic [15:0]       s8x16up_out[1:0][0:3],
    input [15:0]              s8x16up_3d_in[1:0][0:1][0:1],
    output logic [15:0]       s8x16up_3d_out[1:0][0:1][0:1],
    input                     clk_en,
    input                     clk /*verilator clocker*/);

   logic [31:0]               secret_accum_q = 0;
   logic [31:0]               secret_value = 7;

   initial $display("created %m");

   logic                      the_clk;
   generate
      if (GATED_CLK != 0) begin: yes_gated_clock
         logic clk_en_latch /*verilator clock_enable*/;
         /* verilator lint_off COMBDLY */
         /* verilator lint_off LATCH */
         always_comb if (clk == '0) clk_en_latch <= clk_en;
         /* verilator lint_on LATCH */
         /* verilator lint_on COMBDLY */
         assign the_clk = clk & clk_en_latch;
      end else begin: no_gated_clock
         assign the_clk = clk;
      end
   endgenerate

   always @(posedge the_clk) begin
      secret_accum_q <= secret_accum_q + accum_in + secret_value;
   end

   // Test combinatorial paths of different sizes
   always @(*) begin
      s1_out = s1_in;
      s1up_out = s1up_in;
      s2_out = s2_in;
      s8_out = s8_in;
      s64_out = s64_in;
      s65_out = s65_in;
      s129_out = s129_in;
      s4x32_out = s4x32_in;
   end

   for (genvar i = 0; i < 3; ++i) begin
      assign s6x16up_out[0][i] = s6x16up_in[0][i];
      assign s6x16up_out[1][i] = s6x16up_in[1][i];
   end
   for (genvar i = 0; i < 4; ++i) begin
      assign s8x16up_out[0][i] = s8x16up_in[0][i];
      assign s8x16up_out[1][i] = s8x16up_in[1][i];
   end
   for (genvar i = 0; i < 8; ++i) begin
      assign s8x16up_3d_out[i[2]][i[1]][i[0]] = s8x16up_3d_in[i[2]][i[1]][i[0]];
   end


   sub sub (.sub_in(s33_in), .sub_out(s33_out));

   // Test sequential path
   assign accum_out = secret_accum_q;

   // Test mixed combinatorial/sequential path
   assign accum_bypass_out = accum_bypass ? accum_in : secret_accum_q;

   final $display("destroying %m");

endmodule

module sub (
            input [32:0]  sub_in,
            output [32:0] sub_out);

   /*verilator no_inline_module*/

   assign sub_out = sub_in;

endmodule
