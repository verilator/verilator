// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  logic [7:0] c;
  logic [7:0] c_param;
  int cycles = 0;

  blk u (
      .clk(clk),
      .cnt_o(c)
  );
  // Type parameter T keeps its default from my_pkg; setting it is unsupported
  blk_param #(
      .STEP(3)
  ) u_param (
      .clk(clk),
      .cnt_o(c_param)
  );

  always @(negedge clk) begin
    cycles = cycles + 1;
    `checkd(c, 8'(cycles));
    `checkd(c_param, 8'(cycles * 3));
    if (cycles == 10) begin
      `checkd(c, 8'd10);
      `checkd(c_param, 8'd30);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
