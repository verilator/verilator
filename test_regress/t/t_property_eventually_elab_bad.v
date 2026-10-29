// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;

  int n = 1;
  localparam string OPAQUE = "";

  property p_lo(lo);
    eventually[lo: 2] 1'b1;
  endproperty
  property p_hi(hi);
    eventually[0: hi] 1'b1;
  endproperty
  property p_range(lo, hi);
    eventually[lo: hi] 1'b1;
  endproperty
  property p_forward(lo, hi);
    p_range(
        lo, hi
    );
  endproperty

  assert property (@(posedge clk) p_lo(n));
  assert property (@(posedge clk) p_hi(n));
  assert property (@(posedge clk) p_lo(-1));
  assert property (@(posedge clk) p_forward(2, 1));
  assert property (@(posedge clk) p_hi($));
  assert property (@(posedge clk) p_lo(OPAQUE));
  assert property (@(posedge clk) p_hi(OPAQUE));
endmodule
