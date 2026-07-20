// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  logic clk;
  int i;
  always #(1) clk = ~clk;
  task automatic taska();
    fork : wait_fork
      begin
        repeat (1) @(negedge clk);
        i = 1;
      end
      begin
        repeat (2) @(negedge clk);
        i = 2;
      end
    join_any
    disable wait_fork;
  endtask

  initial begin
    clk = '0;
    fork
      taska();
      taska();
    join
    `checkd(i, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
