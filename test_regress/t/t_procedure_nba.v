// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk;
  initial clk = 0;
  always #5 clk = ~clk;
  bit [99:0][2:0] foo;
  bit bar;

  always @(posedge clk) begin
    bar <= ~bar;
    #1;
  end

  genvar i;
  for (i = 0; i < 100; i=i+1)
    `PROCEDURE begin
      foo[i] <= 3;
      if (foo[i] !== 0) $stop;
      @(posedge clk);
      if (foo[i] !== 3) $stop;
      foo[i] = 2;
      if (foo[i] !== 2) $stop;
      #1;
      if (foo[i] !== 2) $stop;
      foo[i] = 0;
    end

  initial #100 begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
