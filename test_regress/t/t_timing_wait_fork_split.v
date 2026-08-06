// DESCRIPTION: Verilator: Verilog Test module
//
// A 'wait fork' needs a dynamic trigger temporary, which is function-local to
// the process it appears in. Splitting the process into sub-functions must not
// separate that declaration from its uses, as sub-functions are emitted as
// separate C++ functions.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 1'b0;
  int   cnt = 0;

  always #5 clk = ~clk;

  task automatic phase(int n);
    fork begin @(posedge clk); cnt += n; end join_none
    wait fork;
  endtask

  initial begin
    fork @(posedge clk); join_none
    wait fork;
    phase(1);
    fork @(negedge clk); join_none
    wait fork;
    phase(2);
    fork @(posedge clk); join_none
    wait fork;
    phase(4);
    if (cnt != 7) begin
      $write("%%Error: cnt=%0d exp=7\n", cnt);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
