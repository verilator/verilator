// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Ethan Sifferman
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  int delay = 0;
  always #1 delay = int'($time) / 4;
  task automatic do_delay;
    // verilator lint_off ZERODLY
    if (delay > 0) #(delay);
    // verilator lint_on ZERODLY
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
    b <= 1;  // this line should do nothing
  end

  always #1 `checkh(a, b)

  initial begin
    #20;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
