// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   wire [1:0]  clkvec = crc[1:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [1:0]           count;                  // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .count                    (count[1:0]),
              // Inputs
              .clkvec                   (clkvec[1:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {62'h0, count};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
         sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
`define EXPECTED_SUM 64'hfe8bac0bb1a0e53b
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

`ifdef T_TEST1
module Test
  (
   input  wire [1:0] clkvec,
   // verilator lint_off MULTIDRIVEN
   output reg  [1:0] count
   // verilator lint_on  MULTIDRIVEN
   );
   genvar            igen;
   generate
      for (igen=0; igen<2; igen=igen+1) begin : code_gen
         initial count[igen] = 1'b0;
         always @ (posedge clkvec[igen])
           count[igen] <= count[igen] + 1;
      end
   endgenerate
   always @ (count) begin
      $write("hi\n");
   end
endmodule
`endif

`ifdef T_TEST2
module Test
  (
   input  wire [1:0] clkvec,
   // verilator lint_off MULTIDRIVEN
   output reg  [1:0] count
   // verilator lint_on  MULTIDRIVEN
   );
   genvar            igen;
   generate
      for (igen=0; igen<2; igen=igen+1) begin : code_gen
         wire clk_tmp = clkvec[igen];
         // Unsupported: Count is multidriven, though if we did better analysis it wouldn't
         // need to be.
         initial count[igen] = 1'b0;
         always @ (posedge clk_tmp)
           count[igen] <= count[igen] + 1;
      end
   endgenerate
endmodule
`endif

`ifdef T_TEST3
module Test
  (
   input  wire [1:0] clkvec,
   output wire [1:0] count
   );
   genvar igen;
   generate
      for (igen=0; igen<2; igen=igen+1) begin : code_gen
         wire clk_tmp = clkvec[igen];
         reg  tmp_count = 1'b0;
         always @ (posedge clk_tmp) begin
            tmp_count <= tmp_count + 1;
         end
         assign count[igen] = tmp_count;
      end
   endgenerate
endmodule
`endif
