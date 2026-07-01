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

  logic rst = 1'b1;
  initial #22 rst = 1'b0;

  logic assertEnable = 1'b0;
  initial #44 assertEnable = 1'b1;

  initial begin
    #1000;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  int cntA = 0;
  int cntB = 100;
  always @(posedge clk) begin
    cntA <= cntA + 1;
    cntB <= cntB + 1;
  end

  // Should combine the 2 assertOn checks after hoisting
  always @(posedge clk) begin
    if (rst) begin
      // Blank
    end
    else if (assertEnable) begin
      assert (cntA == cntB - 100);
      labelled_A : assert (cntB - cntA == 100);
    end
  end

  // Should combine the 2 assertOn checks after hoisting
  always @(posedge clk) begin
    if (assertEnable) begin
      labelled_B : assert (cntA + 100 == cntB);
    end
    if (!assertEnable) begin
      // Blank
    end
    else begin
      assert (cntA - cntB == -100);
    end
  end

  // Should combine the 2 nested assertOn checks after hoisting
  always @(posedge clk) begin
    if (assertEnable) begin
      // This is an 'assert' with another 'assert' in the fail branch
      assert(cntB - 100 == cntA); else assert(cntB == cntA + 100);
    end
  end

endmodule
