// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Marco Brambilla
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic a = 0, b = 0;

  // a in cycle 3, b in cycle 6: both properties hold
  assert property (@(posedge clk) a |=> s_eventually b);
  assert property (@(posedge clk) a |-> s_eventually b);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= (cyc == 2);
    b <= (cyc == 5);
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
