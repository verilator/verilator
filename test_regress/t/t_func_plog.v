// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;
   reg          rst_n;

   // Take CRC data and apply to testblock inputs

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [2:0]           pos1;                   // From test of Test.v
   wire [2:0]           pos2;                   // From test of Test.v
   // End of automatics

   Test test (
              // Outputs
              .pos1                     (pos1[2:0]),
              .pos2                     (pos2[2:0]),
              /*AUTOINST*/
              // Inputs
              .clk                      (clk),
              .rst_n                    (rst_n));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {61'h0, pos1};

   // What checksum will we end up with
`define EXPECTED_SUM 64'h039ea4d039c2e70b

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      rst_n <= ~1'b0;
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         rst_n <= ~1'b1;
      end
      else if (cyc<10) begin
         sum <= 64'h0;
         rst_n <= ~1'b1;
      end
      else if (cyc<90) begin
         if (pos1 !== pos2) $stop;
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test
  #(parameter SAMPLE_WIDTH = 5 )
   (
`ifdef verilator  // Some simulators don't support clog2
    output reg [$clog2(SAMPLE_WIDTH)-1:0]         pos1,
`else
    output reg [log2(SAMPLE_WIDTH-1)-1:0]         pos1,
`endif
    output reg [log2(SAMPLE_WIDTH-1)-1:0]         pos2,
    // System
    input       clk,
    input       rst_n
    );

   function integer log2(input integer arg);
      begin
         for(log2=0; arg>0; log2=log2+1)
           arg = (arg >> 1);
      end
   endfunction

   always @ (posedge clk or negedge  rst_n)
     if (!rst_n) begin
        pos1 <= 0;
        pos2 <= 0;
     end
     else begin
        pos1 <= pos1 + 1;
        pos2 <= pos2 + 1;
     end
endmodule
