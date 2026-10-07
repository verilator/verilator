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

  int cnt = 0;
  function automatic logic [7:0] f();
    ++cnt;
    return 8'd3;
  endfunction

  // Comparisons that are constant due to unsigned arithmetic or limited range,
  // but have an operand with side effects that must still be evaluated
  initial begin
    logic r;
    // UNSIGNED
    r = f() < 8'd0;
    `checkd(r, 1'b0);
    `checkd(cnt, 1);
    r = f() >= 8'd0;
    `checkd(r, 1'b1);
    `checkd(cnt, 2);
    r = 8'd0 > f();
    `checkd(r, 1'b0);
    `checkd(cnt, 3);
    r = 8'd0 <= f();
    `checkd(r, 1'b1);
    `checkd(cnt, 4);
    // CMPCONST
    r = f() > 8'hff;
    `checkd(r, 1'b0);
    `checkd(cnt, 5);
    r = f() <= 8'hff;
    `checkd(r, 1'b1);
    `checkd(cnt, 6);
    r = 8'hff < f();
    `checkd(r, 1'b0);
    `checkd(cnt, 7);
    r = 8'hff >= f();
    `checkd(r, 1'b1);
    `checkd(cnt, 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
