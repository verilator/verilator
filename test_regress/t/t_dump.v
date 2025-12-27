// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

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

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0]          out;                    // From test of Test.v
   // End of automatics

   Test test(/*AUTOINST*/
             // Outputs
             .out                       (out[31:0]),
             // Inputs
             .clk                       (clk),
             .in                        (in[31:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (cyc == 0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc < 10) begin
         sum <= '0;
      end
      else if (cyc < 90) begin
      end
      else if (cyc == 99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h4afe43fb79d7b71e
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test(/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, in
   );

   // Replace this module with the device under test.
   //
   // Change the code in the t module to apply values to the inputs and
   // merge the output values into the result vector.

   input clk;
   input [31:0] in;
   output reg [31:0] out;

   always @(posedge clk) begin
      out <= in;

      // Assert control dump test.
      $assertoff;
      $assertkill;
      assert(0);
      $asserton;
      $assertcontrol(3, 8);
      begin : blk
         disable blk;
      end
   end
   initial begin
      assert_simple_immediate_else: assert(0) else $display("fail");
      assert_simple_immediate_stmt: assert(0) $display("pass");
      assert_simple_immediate_stmt_else: assert(0) $display("pass"); else $display("fail");

      assume_simple_immediate: assume(0);
      assume_simple_immediate_else: assume(0) else $display("fail");
      assume_simple_immediate_stmt: assume(0) $display("pass");
      assume_simple_immediate_stmt_else: assume(0) $display("pass"); else $display("fail");
   end

   assert_observed_deferred_immediate: assert #0 (0);
   assert_observed_deferred_immediate_else: assert #0 (0) else $display("fail");
   assert_observed_deferred_immediate_stmt: assert #0 (0) $display("pass");
   assert_observed_deferred_immediate_stmt_else: assert #0 (0) $display("pass"); else $display("fail");

   assume_observed_deferred_immediate: assume #0 (0);
   assume_observed_deferred_immediate_else: assume #0 (0) else $display("fail");
   assume_observed_deferred_immediate_stmt: assume #0 (0) $display("pass");
   assume_observed_deferred_immediate_stmt_else: assume #0 (0) $display("pass"); else $display("fail");

   assert_final_deferred_immediate: assert final (0);
   assert_final_deferred_immediate_else: assert final (0) else $display("fail");
   assert_final_deferred_immediate_stmt: assert final (0) $display("pass");
   assert_final_deferred_immediate_stmt_else: assert final (0) $display("pass"); else $display("fail");

   assume_final_deferred_immediate: assume final (0);
   assume_final_deferred_immediate_else: assume final (0) else $display("fail");
   assume_final_deferred_immediate_stmt: assume final (0) $display("pass");
   assume_final_deferred_immediate_stmt_else: assume final (0) $display("pass"); else $display("fail");

   property prop();
      @(posedge clk) 0
   endproperty

   assert_concurrent: assert property (prop);
   assert_concurrent_else: assert property(prop) else $display("fail");
   assert_concurrent_stmt: assert property(prop) $display("pass");
   assert_concurrent_stmt_else: assert property(prop) $display("pass"); else $display("fail");

   assume_concurrent: assume property(prop);
   assume_concurrent_else: assume property(prop) else $display("fail");
   assume_concurrent_stmt: assume property(prop) $display("pass");
   assume_concurrent_stmt_else: assume property(prop) $display("pass"); else $display("fail");

   cover_concurrent: cover property(prop);
   cover_concurrent_stmt: cover property(prop) $display("pass");

   restrict property (prop);

   always_ff @(posedge clk) begin
     unique0 casez(in)
       1: $display("1a");
       default: $display("1b");
     endcase
     priority casez(1'b1)
       in[0]: $display("2a");
       default: $display("2b");
     endcase
   end

endmodule
