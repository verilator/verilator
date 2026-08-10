// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;

  bit clk = 0;
  int cyc = 0;
  bit a = 0, b = 0, c = 0, abrt = 0;
  int fail_bool = 0;
  int fail_seq = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= cyc[0];
    b <= cyc[1];
    c <= cyc[2];
    abrt <= (cyc == 7);
  end

  assert property (@(posedge clk) sync_accept_on (abrt) (b |-> c)) else fail_bool++;
  assert property (@(posedge clk) sync_accept_on (abrt) ((a ##1 b) |-> c)) else fail_seq++;

  initial begin
    repeat (40) #5 clk = ~clk;
    `checkd(fail_bool, 5);
    `checkd(fail_seq, 3);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
