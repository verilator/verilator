// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  task phase();
    #1000;
    $display("ended");
  endtask

  initial begin
    fork
      phase();
    join_none
    #123;
    $display("[%0t] $finish", $time);
    $finish;
  end

  final begin
    $display("[%0t] final", $time);
    `checkd($time, 123);
  end

endmodule
