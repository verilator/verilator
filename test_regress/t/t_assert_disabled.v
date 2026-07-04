// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer action_hits = 0;
  integer cyc = 0;

  assert property (@(posedge clk) ##1 1'b1) action_hits++;
  else action_hits--;

  always @(posedge clk) begin
    cyc++;
    assert (0);
    if (cyc == 4) begin
      `checkd(action_hits, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
