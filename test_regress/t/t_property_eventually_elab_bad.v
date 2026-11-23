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

  property p_strong(lo, hi);
    s_eventually[lo: hi] 1'b1;
  endproperty
  assert property (@(posedge clk) p_strong(n, $));
  assert property (@(posedge clk) p_strong(0, n));
  assert property (@(posedge clk) p_strong(3, 2));

  localparam UNBOUNDED = $;
  assert property (@(posedge clk) s_eventually[UNBOUNDED:3] clk);

  localparam int HI[2] = '{1, 2};
  assert property (@(posedge clk) eventually[0:HI] clk);

  localparam X_BOUND = 2'b0x;
  localparam Z_BOUND = 2'b1z;
  assert property (@(posedge clk) eventually[X_BOUND:2] clk);
  assert property (@(posedge clk) s_eventually[0:Z_BOUND] clk);
  assert property (@(posedge clk) p_hi(X_BOUND));
  assert property (@(posedge clk) p_strong(Z_BOUND, $));
endmodule
