// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
  input clk
);
  integer cyc = 0;
  reg [63:0] crc = '0;
  reg [63:0] sum = '0;

  // Derive test signals from CRC
  wire a = crc[0];
  wire b = crc[1];
  wire c = crc[2];
  wire d = crc[3];

  wire [63:0] result = {60'h0, d, c, b, a};

  always_ff @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x a=%b b=%b c=%b d=%b\n",
           $time, cyc, crc, a, b, c, d);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};

    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= '0;
    end else if (cyc < 10) begin
      sum <= '0;
    end else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkh(sum, 64'hdb7bc8bfe61f987e);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // =========================================================================
  // Boolean intersect (length-0): equivalent to boolean AND (IEEE 16.9.6)
  // =========================================================================

  // Boolean intersect: when a & b, intersect succeeds (equivalent to AND)
  assert property (@(posedge clk) disable iff (cyc < 2)
      (a & b) |-> (a intersect b));

  // Boolean intersect with constant true -- reduces to just 'a'
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> (a intersect 1'b1));

  // =========================================================================
  // Multi-cycle sequence intersect (IEEE 1800-2023 16.9.6)
  // Same-length sequences: intersect succeeds when both arms complete
  // =========================================================================

  // Both arms have length 1; 1'b1 guarantees completion on both sides
  assert property (@(posedge clk)
      (a & b) |-> (a ##1 1'b1) intersect (b ##1 1'b1));

  // Both arms have length 2
  assert property (@(posedge clk)
      (a & b) |-> (a ##2 1'b1) intersect (b ##2 1'b1));

  // Different internal structure, same total length (2 cycles each)
  assert property (@(posedge clk)
      (a & b) |-> (a ##1 1'b1 ##1 1'b1) intersect (b ##2 1'b1));

  // Standalone constant intersect (always passes)
  assert property (@(posedge clk)
      (1'b1 ##1 1'b1) intersect (1'b1 ##1 1'b1));

endmodule
