// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-threaded scheduling hazard on combinational loop variables.

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  logic [31:0] cyc = 0;

  // verilator lint_off UNOPTFLAT
  logic xxx, yyy;
  // verilator lint_on UNOPTFLAT

  // verilator lint_off ALWCOMBORDER
  always_comb xxx = cyc[0] ? ~yyy : xxx;  // xxx will become hybrid sensitivity
  always_comb yyy = cyc[0] ? ~xxx : yyy;  // yyy will become hybrid sensitivity
  // verilator lint_on ALWCOMBORDER

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      $display("xxx^yyy=%x", xxx ^ yyy);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
