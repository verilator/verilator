// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Ethan Sifferman
// SPDX-License-Identifier: CC0-1.0

module t;

  int delay = 0; always #1 delay = int'($time) / 4;
  task automatic do_delay;
    if (delay > 0) #(delay);
  endtask

  // `a` should match `b`
  logic a = 0;
  always begin
    a <= 1;
    do_delay();
    a <= 0;

    #1;
  end

  logic b = 0;
  always begin
    b <= 1;
    do_delay();
    b <= 0;

    #1;
    b <= 1; // this line should do nothing
  end

  always #1 assert (a == b);

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #20;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
