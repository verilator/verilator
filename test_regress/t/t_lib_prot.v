// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

`define DRIVE(sig) \
/* Just throw a bunch of bits at the input */ \
/* verilator lint_off WIDTH */ \
sig``_in <= {8{crc}}; \
/* verilator lint_on WIDTH */
`define CHECK(sig) \
if (cyc > 0 && sig``_in != sig``_out) begin \
   $display(`"%%Error (%m) sig``_in (0x%0x) != sig``_out (0x%0x)`", \
            sig``_in, sig``_out); \
     $stop; \
       end

module t #(parameter GATED_CLK = 0) (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   localparam last_cyc =
`ifdef TEST_BENCHMARK
              `TEST_BENCHMARK;
`else
   10;
`endif

   genvar     x;
   generate
      for (x = 0; x < 2; x = x + 1) begin: gen_loop
         integer cyc = 0;
         reg [63:0] crc = 64'h5aef0c8d_d70a4497;
         logic [31:0] accum_in;
         logic [31:0] accum_out;
         logic        accum_bypass;
         logic [31:0] accum_bypass_out;
         logic [31:0] accum_out_expect;
         logic [31:0] accum_bypass_out_expect;
         logic        s1_in;
         logic        s1_out;
         logic        s1up_in[2];
         logic        s1up_out[2];
         logic [1:0]  s2_in;
         logic [1:0]  s2_out;
         logic [7:0]  s8_in;
         logic [7:0]  s8_out;
         logic [32:0] s33_in;
         logic [32:0] s33_out;
         logic [63:0] s64_in;
         logic [63:0] s64_out;
         logic [64:0] s65_in;
         logic [64:0] s65_out;
         logic [128:0] s129_in;
         logic [128:0] s129_out;
         logic [3:0] [31:0] s4x32_in;
         logic [3:0] [31:0] s4x32_out;
         /*verilator lint_off LITENDIAN*/
         logic [0:15]       s6x16up_in[0:1][2:0];
         logic [0:15]       s6x16up_out[0:1][2:0];
         /*verilator lint_on LITENDIAN*/
         logic [15:0]       s8x16up_in[1:0][0:3];
         logic [15:0]       s8x16up_out[1:0][0:3];
         logic [15:0]       s8x16up_3d_in[1:0][0:1][0:1];
         logic [15:0]       s8x16up_3d_out[1:0][0:1][0:1];

         wire               clk_en = crc[0];

         secret
           secret (
                   .accum_in,
                   .accum_out,
                   .accum_bypass,
                   .accum_bypass_out,
                   .s1_in,
                   .s1_out,
                   .s1up_in,
                   .s1up_out,
                   .s2_in,
                   .s2_out,
                   .s8_in,
                   .s8_out,
                   .s33_in,
                   .s33_out,
                   .s64_in,
                   .s64_out,
                   .s65_in,
                   .s65_out,
                   .s129_in,
                   .s129_out,
                   .s4x32_in,
                   .s4x32_out,
                   .s6x16up_in,
                   .s6x16up_out,
                   .s8x16up_in,
                   .s8x16up_out,
                   .s8x16up_3d_in,
                   .s8x16up_3d_out,
                   .clk_en,
                   .clk);

         always @(posedge clk) begin
`ifdef TEST_VERBOSE
            $display("[%0t] x=%0d, cyc=%0d accum_in=%0d accum_out=%0d accum_bypass_out=%0d",
                     $time, x, cyc, accum_in, accum_out, accum_bypass_out);
`endif
            cyc <= cyc + 1;
            crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
            accum_in <= accum_in + 5;
            `DRIVE(s1)
            `DRIVE(s2)
            `DRIVE(s8)
            `DRIVE(s33)
            `DRIVE(s64)
            `DRIVE(s65)
            `DRIVE(s129)
            `DRIVE(s4x32)
            {s1up_in[1], s1up_in[0]} <= {^crc, ~(^crc)};
            {s6x16up_in[0][0], s6x16up_in[0][1], s6x16up_in[0][2]} <= crc[47:0];
            {s6x16up_in[1][0], s6x16up_in[1][1], s6x16up_in[1][2]} <= ~crc[63:16];
            {s8x16up_in[0][0], s8x16up_in[0][1], s8x16up_in[0][2], s8x16up_in[0][3]} <= crc;
            {s8x16up_in[1][0], s8x16up_in[1][1], s8x16up_in[1][2], s8x16up_in[1][3]} <= ~crc;
            {s8x16up_3d_in[0][0][0], s8x16up_3d_in[0][0][1]} <= ~crc[31:0];
            {s8x16up_3d_in[0][1][0], s8x16up_3d_in[0][1][1]} <= ~crc[63:32];
            {s8x16up_3d_in[1][0][0], s8x16up_3d_in[1][0][1]} <= crc[31:0];
            {s8x16up_3d_in[1][1][0], s8x16up_3d_in[1][1][1]} <= crc[63:32];
            if (cyc == 0) begin
               accum_in <= x*100;
               accum_bypass <= '0;
            end else if (cyc > 0) begin
               if (accum_out_expect != accum_out) begin
                  $display("%%Error: (%m) accum_out expected %0d got %0d",
                           accum_out_expect, accum_out);
                  $stop;
               end
               if (accum_bypass_out_expect != accum_bypass_out) begin
                  $display("%%Error: (%m) accum_bypass_out expected %0d got %0d",
                           accum_bypass_out_expect, accum_bypass_out);
                  $stop;
               end
            end

            if (cyc == 5) accum_bypass <= '1;

            if (x == 0 && cyc == last_cyc) begin
               $display("final cycle = %0d", cyc);
               $write("*-* All Finished *-*\n");
               $finish;
            end
         end

         logic possibly_gated_clk;
         if (GATED_CLK != 0) begin: yes_gated_clock
            logic clk_en_latch /*verilator clock_enable*/;
            /* verilator lint_off COMBDLY */
            /* verilator lint_off LATCH */
            always_comb if (clk == '0) clk_en_latch <= clk_en;
            /* verilator lint_on LATCH */
            /* verilator lint_on COMBDLY */
            assign possibly_gated_clk = clk & clk_en_latch;
         end else begin: no_gated_clock
            assign possibly_gated_clk = clk;
         end

         always @(posedge possibly_gated_clk) begin
            // 7 is the secret_value inside the secret module
            accum_out_expect <= accum_in + accum_out_expect + 7;
         end

         always @(*) begin
            // XSim (and maybe all event simulators?) sees the moment where
            // s1_in has not yet propagated to s1_out, however, they do always
            // both change at the same time
            /* verilator lint_off STMTDLY */
            #1;
            /* verilator lint_on STMTDLY */
            `CHECK(s1)
            `CHECK(s1up)
            `CHECK(s2)
            `CHECK(s8)
            `CHECK(s33)
            `CHECK(s64)
            `CHECK(s65)
            `CHECK(s129)
            `CHECK(s4x32)
            `CHECK(s6x16up)
            `CHECK(s8x16up)
            `CHECK(s8x16up_3d)
         end

         assign accum_bypass_out_expect = accum_bypass ? accum_in :
                                          accum_out_expect;
      end
   endgenerate

endmodule
