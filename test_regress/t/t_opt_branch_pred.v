// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc = 0;
  reg [7:0] a = 0;
  reg [7:0] b = 0;

  task automatic report(input integer value);
    /*verilator no_inline_task*/
    $display("report %0d", value);
  endtask

  always @(posedge clk) begin
    cyc <= cyc + 1;
    // Then branch unlikely
    if (cyc == 99) $display("then %0d", cyc);
    // Else branch unlikely
    if (cyc != 98) a <= a + 1;
    else $display("else %0d", cyc);
    // Unlikely in both branches, left unknown
    if (cyc[0]) $display("odd");
    else $display("even");
    // Only the nested 'if' is unlikely, not its enclosing branch
    if (cyc[1]) begin
      b <= b + 1;
      if (b == 97) $display("nested %0d", b);
    end
    // Left unknown, as only the called function holds unlikely statements
    if (cyc == 96) report(cyc);
    // Then branch unlikely
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
