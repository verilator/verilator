// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.

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

module t (/*AUTOARG*/
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

   genvar x;
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

         wire clk_en = crc[0];

         secret
           secret (
                   .accum_in,
                   .accum_out,
                   .accum_bypass,
                   .accum_bypass_out,
                   .s1_in,
                   .s1_out,
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
                   .clk_en,
                   .clk);

         always @(posedge clk) begin
`ifdef TEST_VERBOSE
            $display("[%0t] x=%0d, cyc=%0d accum_in=%0d accum_out=%0d accum_bypass_out=%0d",
                     $time, x, cyc, accum_in, accum_out, accum_bypass_out);
`endif
            cyc <= cyc + 1;
            crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
            accum_in <= accum_in + 5;
            // 7 is the secret_value inside the secret module
            accum_out_expect <= accum_in + accum_out_expect + 7;
            `DRIVE(s1)
            `DRIVE(s2)
            `DRIVE(s8)
            `DRIVE(s33)
            `DRIVE(s64)
            `DRIVE(s65)
            `DRIVE(s129)
            `DRIVE(s4x32)
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

         always @(*) begin
            // XSim (and maybe all event simulators?) sees the moment where
            // s1_in has not yet propagated to s1_out, however, they do always
            // both change at the same time
            /* verilator lint_off STMTDLY */
            #1;
            /* verilator lint_on STMTDLY */
            `CHECK(s1)
            `CHECK(s2)
            `CHECK(s8)
            `CHECK(s33)
            `CHECK(s64)
            `CHECK(s65)
            `CHECK(s129)
            `CHECK(s4x32)
         end

         assign accum_bypass_out_expect = accum_bypass ? accum_in :
                                          accum_out_expect;
      end
   endgenerate

endmodule
