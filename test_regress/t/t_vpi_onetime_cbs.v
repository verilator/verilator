// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// SPDX-FileCopyrightText: 2020 Wilson Snyder and Marlon James
// SPDX-License-Identifier: CC0-1.0


module t;

  logic clk;
  initial begin
    clk = 0;
    #10;
    while ($time < 100) begin
      clk = !clk;
      #10;
    end
  end

  reg [31:0] count  /*verilator public_flat_rd */;

  // Test loop
  initial begin
    count = 0;
  end

  always @(posedge clk) begin
    count <= count + 2;
  end

endmodule
