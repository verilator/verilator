// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/
   clk
);
  input clk;

  typedef struct {
    int x;
    int y;
  } s_t;
  s_t brk[100];
  s_t wrt[100];
  int cyc = 0;

  task automatic skip(ref int idx);
    idx = 100;
  endtask

  // These loops count past --unroll-count, but stop early, so must still be unrolled for the
  // nonblocking assignments to arrays of structs
  always @(posedge clk) begin
    cyc <= cyc + 1;
    for (int i = 0; i < 100; ++i) begin
      brk[i] <= '{x: cyc + i, y: i};
      if (i == 3) break;
    end
    for (int i = 0; i < 100; ++i) begin
      wrt[i] <= '{x: cyc + i, y: i};
      if (i == 3) skip(i);
    end
    if (cyc > 0) begin
      `checkd(brk[3].x, cyc + 2);
      `checkd(brk[3].y, 3);
      `checkd(brk[4].x, 0);
      `checkd(wrt[3].x, cyc + 2);
      `checkd(wrt[3].y, 3);
      `checkd(wrt[4].x, 0);
    end
    if (cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
