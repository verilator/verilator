// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%p exp='h%p\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

`define PROPERTY_CHECK(msg) \
    $display("[%0t] stmt, %s, fileline:%d", $time, msg, `__LINE__); \
  else \
    $display("[%0t] else, %s, fileline:%d", $time, msg, `__LINE__); \

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;

  localparam MAX = 4;
  integer cyc = 1;

  assert property (@(negedge clk) disable iff (cyc < MAX - 1) s_eventually (cyc == MAX - 1)) `PROPERTY_CHECK("s_eventually before final")

  assert property (@(negedge clk) disable iff (cyc < MAX - 1) s_eventually (cyc == MAX)) `PROPERTY_CHECK("s_eventually during final")

  assert property (@(negedge clk) disable iff (cyc < MAX - 1) s_eventually (cyc == MAX + 1)) `PROPERTY_CHECK("s_eventually after final")

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
