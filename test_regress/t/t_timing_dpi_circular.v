// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  reg rtl_clk;
  initial begin
    rtl_clk = 1'b0;
    forever #2 rtl_clk = ~rtl_clk;
  end

  export "DPI-C" pong = task pong;
  task pong(input int n, output int o);
    $display("%t: Called pong(%d)", $time, n);
    @(posedge rtl_clk);
    ping(n - 1, o);
  endtask

  import "DPI-C" context task ping(
    input  int n,
    output int res
  );

  int res;
  initial begin
    res = 0;
    ping(10, res);
    $display("res = %d", res);
    $finish;
  end
endmodule
