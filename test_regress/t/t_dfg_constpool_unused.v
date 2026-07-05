// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 1'b0;
  always #5 clk = ~clk;

  logic [31:0] cyc = 0;

  // Converted to case table in const pool, but proven unused by Dfg
  logic [15:0] out;
  always_comb begin
    case (cyc[3:0])
      4'd0: out = 16'h1111;
      4'd1: out = 16'h2222;
      4'd2: out = 16'h4444;
      4'd3: out = 16'h8888;
      default: out = 16'h0f0f;
    endcase
  end

  // Complicated way to write constant 0 that only Dfg can decipher
  wire [63:0] convoluted_zero = (({64{cyc[0]}} & ~{64{cyc[0]}}));

  wire logic [15:0] zero = &convoluted_zero ? out : 16'd0;

  // Test driver/checker
  always @(posedge clk) begin
    `checkh(zero, 16'd0);
    cyc <= cyc + 32'd1;
    if (cyc == 32'd32) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
