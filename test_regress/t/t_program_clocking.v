// DESCRIPTION: Verilator: Program clocking event scheduling test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

program t;
  bit woke_at_first_event = 0;
  bit woke_at_dynamic_event = 0;
  bit checked_clocking_output = 0;

  initial begin
    #1;
    `checkd(int'($time), 1)
    @(tb_top.mck);
    `checkd(int'($time), 3)
    #1;
    `checkd(woke_at_first_event, 1)
    `checkd(woke_at_dynamic_event, 1)
    `checkd(checked_clocking_output, 1)
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    @(tb_top.mck);
    `checkd(int'($time), 1)
    woke_at_first_event = 1;
  end

  initial begin
    fork
      #1 woke_at_dynamic_event = 1;
    join_none
    wait fork;
    `checkd(int'($time), 1)
    `checkd(woke_at_dynamic_event, 1)
  end

  initial begin
    @(tb_top.mck);
    tb_top.mck.driven <= 1;
    @(tb_top.mck);
    `checkd(int'($time), 3)
    `checkd(tb_top.driven, 1)
    checked_clocking_output = 1;
  end
endprogram

module tb_top;
  bit clk = 0;
  bit driven = 0;
  t test ();
  always #1 clk = ~clk;
  clocking mck @(posedge clk);
    output #0 driven;
  endclocking
endmodule
