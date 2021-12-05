// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   wire [63:0] result;

   Test test(/*AUTOINST*/
             // Outputs
             .result                    (result[63:0]),
             // Inputs
             .clk                       (clk),
             .cyc                       (cyc));


   reg [63:0] sum;

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d result=%x\n", $time, cyc, result);
`endif
      cyc <= cyc + 1;
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (cyc == 0) begin
         // Setup
         sum <= '0;
      end
      else if (cyc < 10) begin
         sum <= '0;
      end
      else if (cyc < 90) begin
      end
      else if (cyc == 99) begin
         $write("[%0t] cyc==%0d sum=%x\n", $time, cyc, sum);
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'hfefad16f06ba6b1f
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test(/*AUTOARG*/
   // Outputs
   result,
   // Inputs
   clk, cyc
   );

   input clk;
   input int cyc;
   output reg [63:0] result;

   logic [63:0]      adder;

   always @(posedge clk) begin
      adder = 0;
      for (int i = 0; i < 1000; ++i)
        adder += {32'h0, (cyc+i)} ** 3;

      result <= adder;
   end
endmodule
