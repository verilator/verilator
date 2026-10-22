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
  int c;

  task automatic count_to(input int n, input bit [6:0] stop_at, output int cnt);
    bit [6:0] local_i;
    for (local_i = 0; int'(local_i) < n; ++local_i) begin
      if (local_i == stop_at) disable count_to;
      ++c;
    end
    cnt = c;
  endtask

  task automatic non_ansi;
    input int n;  // Non-ansi
    int local_j;
    output int res;
    local_j = n + 1;
    res = local_j;
    disable non_ansi;
    res = 0;
  endtask

  int cnt;
  int res;
  initial begin
    c = 0;
    count_to(10, 3, cnt);
    `checkd(c, 3);

    c = 0;
    count_to(2, 3, cnt);
    `checkd(c, 2);
    `checkd(cnt, 2);

    non_ansi(4, res);
    `checkd(res, 5);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
