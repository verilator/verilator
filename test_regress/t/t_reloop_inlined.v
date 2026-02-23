// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk1 = 1'b0;
  bit clk2 = 1'b0;
  always #5 clk1 = ~clk1;
  always #10 clk2 = ~clk2;

  int iarray [63:0];
  int oarray1 [63:0];
  int oarray2 [63:0];

  initial begin
    for (int i = 0; i < 64 ; i = i + 1) begin
      iarray[i] = i;
    end

    #100;

    for (int i = 0; i < 64; i = i + 1) begin
      $display("%d %d %d", i, oarray1[i], oarray2[i]);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

  always @(posedge clk1) begin
    for (int i = 0; i < 64 ; i = i + 1) begin
      oarray1[i] = iarray[i];
    end
  end
  always @(posedge clk2) begin
    for (int i = 0; i < 64 ; i = i + 1) begin
      oarray2[i] =iarray[i];
    end
  end

endmodule
