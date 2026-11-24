// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit ready;
  int constant_value;
  int immediate_value;
  int suspended_value;
  int fork_value;

  initial begin
    wait (1) constant_value = 7;
    `checkd(constant_value, 7);
    ready = 1;
    wait (ready) immediate_value = 8;
    `checkd(immediate_value, 8);
    ready = 0;
    fork
      begin
        #1;
        ready = 1;
      end
    join_none
    wait (ready) suspended_value = 9;
    `checkd(suspended_value, 9);
    fork
      #1 fork_value = 10;
    join_none
    wait fork;
    `checkd(fork_value, 10);
    wait fork;
    fork_value = 11;
    `checkd(fork_value, 11);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
