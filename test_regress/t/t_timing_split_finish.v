// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A $finish in a forked process, inside a statement too large to stay in the
// coroutine: no statement of the process may run after it.

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int count = 0;
  int acc = 0;

  task automatic work(input int v);
    acc += v * 3 + 1;
    acc ^= v;
    acc += acc % 7;
    if (acc > 100000) acc -= 100000;
  endtask

  initial begin
    fork
      begin
        for (int i = 0; i < 4; i++) begin
          @(posedge clk);
          if (i == 2) begin
            work(1); work(2); work(3); work(4); work(5); work(6); work(7); work(8);
            work(9); work(10); work(11); work(12); work(13); work(14); work(15); work(16);
            $write("*-* All Finished *-*\n");
            $finish;
          end
          // Large enough to be moved out on its own
          work(i); work(i + 1); work(i + 2); work(i + 3); work(i + 4); work(i + 5);
          count++;
        end
      end
    join_none
  end

  final `checkd(count, 2);
endmodule
