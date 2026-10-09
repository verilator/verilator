// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Zizhen Liu
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  reg [1:0] p;
  reg [3:0] src;
  wire signed [1:0] base;
  wire [3:0] y = src[base+:4];

  assign base = $signed(p);

  integer cyc = 0;

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d p=%0d base=%0d src=%x y=%b\n", $time, cyc, p, base, src, y);
`endif
    cyc <= cyc + 1;
    // Vary the selected value so the select cannot be constant folded
    src <= src + 4'd1;
    if (cyc == 0) begin
      // Setup
      src <= 4'h9;
      p <= 2'd0;
    end
    else if (cyc == 1) begin
      // base = 0: selects bits 0..3, all in range
      `checkh(y, src);
      p <= 2'd1;
    end
    else if (cyc == 2) begin
      // base = 1: selects bits 1..4, bit 4 is out of range, so only bits 2..0 are compared
      `checkh(y[2:0], src[3:1]);
      p <= 2'd2;
    end
    else if (cyc == 3) begin
      // base = -2: selects bits -2..1, bits -2 and -1 are out of range, so only bits 3..2
      // are compared
      `checkh(y[3:2], src[1:0]);
      p <= 2'd3;
    end
    else if (cyc == 4) begin
      // base = -1: selects bits -1..2, bit -1 is out of range, so only bits 3..1 are compared
      `checkh(y[3:1], src[2:0]);
      p <= 2'd0;
    end
    else if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
