// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: off

`define iteration_count 300
`define expected_end_time 1198

module t;
  reg rtl_clk;
  longint expected_time = 0;

  initial begin
    rtl_clk = 1'b0;
    forever #2 begin
        rtl_clk = ~rtl_clk;
        expected_time = expected_time + 2;
    end
  end

  export "DPI-C" pong = task pong;
  task pong(input int n);
    $display("%t: Called pong(%d)", $time, n);
    @(posedge rtl_clk);
    `checkd($time, expected_time);
    ping(n - 1);
  endtask

  import "DPI-C" context task ping(
    input  int n
  );

  initial begin
    ping(`iteration_count);
    `checkd($time, `expected_end_time);
    $finish;
  end
endmodule
