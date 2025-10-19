// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc = 0;
  reg [63:0] crc;
  reg [63:0] sum;

  // Take CRC data and apply to testblock inputs
  wire [7:0] a = crc[7:0];
  wire [7:0] b = crc[15:8];

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  wire [63:0]           out;                    // From test of Test.v
  wire [63:0]           out2;                   // From test of Test.v
  // End of automatics

  Test test (  /*AUTOINST*/
             // Outputs
             .out                       (out[63:0]),
             .out2                      (out2[63:0]),
             // Inputs
             .clk                       (clk),
             .a                         (a[7:0]),
             .b                         (b[7:0]));

  // Aggregate outputs into a single result vector
  wire [63:0] result = {out};

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
    if (cyc == 0) begin
      // Setup
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= 64'h0;
    end
    else if (cyc < 10) begin
      sum <= 64'h0;
    end
    else if (cyc < 90) begin
      if (out2 !== out) $stop;
    end
    else if (cyc == 99) begin
      $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
      if (crc !== 64'hc77bb9b3784ea091) $stop;
      // What checksum will we end up with (above print should match)
      `define EXPECTED_SUM 64'h0908a1f2194d24ee
      if (sum !== `EXPECTED_SUM) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test (
    input clk,
    input [7:0] a,
    input [7:0] b,
    output reg [63:0] out,
    output reg [63:0] out2
);

  // Also cover comma syntax
  and u0a[7:0] (out[7:0], a[7:0], b[7:0]), u0b[7:0] (out2[7:0], a[7:0], b[7:0]);
  and u1a[7:0] (out[15:8], a[0], b[7:0]), u1b[7:0] (out2[15:8], a[0], b[7:0]);
  and u2a[7:0] (out[23:16], a[0], b[0]), u2b[7:0] (out2[23:16], a[0], b[0]);
  nand u3a[7:0] (out[31:24], a[0], b[7:0]), u3b[7:0] (out2[31:24], a[0], b[7:0]);
  or u4a[7:0] (out[39:32], a[0], b[7:0]), u4b[7:0] (out2[39:32], a[0], b[7:0]);
  nor u5a[7:0] (out[47:40], a[0], b[7:0]), u5b[7:0] (out2[47:40], a[0], b[7:0]);
  xor u6a[7:0] (out[55:48], a[0], b[7:0]), u6b[7:0] (out2[55:48], a[0], b[7:0]);
  xnor u7a[7:0] (out[63:56], a[0], b[7:0]), u7b[7:0] (out2[63:56], a[0], b[7:0]);

endmodule
