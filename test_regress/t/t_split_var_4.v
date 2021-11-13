// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

`ifdef ENABLE_SPLIT_VAR
`define SPLIT_VAR_COMMENT /* verilator split_var */
`else
`define SPLIT_VAR_COMMENT
/* verilator lint_off UNOPTFLAT */
`endif

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   reg [63:0] crc;
   reg [63:0] sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0] in = crc[31:0];
   wire o0;

   wire [15:0] vec_i = crc[15:0];
   wire [31:0] i = crc[31:0];

   Test test(/*AUTOINST*/
             // Outputs
             .o0                        (o0),
             // Inputs
             .clk                       (clk),
             .i                         (i[1:0]));

   // Aggregate outputs into a single result vector
   // verilator lint_off WIDTH
   wire [63:0] result = {o0};
   // verilator lint_on WIDTH

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
      $display("o %b", o0);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (cyc == 0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc == 99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'hb58b16c592557b30
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test(/*AUTOARG*/
   // Outputs
   o0,
   // Inputs
   clk, i
   );

   input wire clk;
   input wire [1:0] i;
   output reg o0;

   typedef struct packed {
      logic v0, v1;
   } packed_type0;
   packed_type0 value0 `SPLIT_VAR_COMMENT;
   wire value0_v0;

   assign value0.v0 = i[0];
   assign value0.v1 = i[1] & !value0_v0;
   assign value0_v0 = value0.v0;

   always_ff @(posedge clk) begin
      o0 <= |value0;
   end
endmodule


`ifdef ENABLE_SPLIT_VAR
/* verilator lint_on UNOPTFLAT */
`endif
