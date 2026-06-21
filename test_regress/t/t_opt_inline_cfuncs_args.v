// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input wire clk
);

  integer cyc = 0;
  reg [31:0] acc;

  task automatic add_pair(input [31:0] a, input [31:0] b, inout [31:0] sum);
    // verilator no_inline_task
    sum = sum + a + b;
  endtask

  always @(posedge clk) begin
    cyc <= cyc + 1;
    acc = 0;
    add_pair(cyc[31:0], 32'd1, acc);  // + cyc + 1
    add_pair(32'd1000, cyc[31:0], acc);  // + 1000 + cyc
    // acc = (cyc + 1) + (1000 + cyc) = 2*cyc + 1001
    if (cyc > 1) begin
      if (acc !== (2 * cyc[31:0] + 32'd1001)) begin
        $write("%%Error: cyc=%0d acc=%0d expected %0d\n", cyc, acc, 2 * cyc + 1001);
        $stop;
      end
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
