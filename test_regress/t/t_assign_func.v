// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc;
  reg [63:0] crc;
  reg [63:0] sum;

  // Take CRC data and apply to testblock inputs
  wire [9:0] a0 = crc[9:0];
  wire [9:0] a1 = crc[19:10];
  wire [9:0] b1 = crc[39:30];
  wire asel = crc[62];
  wire bsel = crc[63];

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  wire [9:0] aq;  // From test of Test.v
  wire [9:0] bq;  // From test of Test.v
  // End of automatics

  Test test (  /*AUTOINST*/
      // Outputs
      .aq(aq[9:0]),
      .bq(bq[9:0]),
      // Inputs
      .a0(a0[9:0]),
      .a1(a1[9:0]),
      .b1(b1[9:0]),
      .asel(asel),
      .bsel(bsel)
  );

  // Aggregate outputs into a single result vector
  wire [63:0] result = {44'h0, aq, bq};

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
      `define EXPECTED_SUM 64'h2c5e6c5e285efafa
      if (sum !== `EXPECTED_SUM) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test (
    input [9:0] a0,
    input [9:0] a1,
    input [9:0] b1,
    input asel,
    input bsel,
    output wire [9:0] aq,
    output wire [9:0] bq
);

  assign aq = MUX10_2(a0, a1, asel);
  assign bq = MUX10_2(aq, b1, bsel);

  function [9:0] MUX10_2;  // Legacy code - not function automatic
    input [9:0] i0;
    input [9:0] i1;
    input [0:0] sel;
    /*static*/ logic [9:0] result;  // Note this is not automatic
    case (sel)
      1'b0: result = i0;
      default: result = i1;
    endcase
    MUX10_2 = result;
  endfunction

endmodule
