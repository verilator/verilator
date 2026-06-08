// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// s_eventually (strong eventually) inside an interface used to trigger an
// internal error in V3Scope ("Can't locate varref scope").

interface my_if (
    input logic clk
);
  logic a;
  assert property (@(posedge clk) s_eventually a);
endinterface

module t (  /*AUTOARG*/);
  bit clk = 0;
  initial forever #1 clk = ~clk;

  integer cyc = 0;

  my_if u_if (.clk(clk));

  initial u_if.a = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    u_if.a <= (cyc >= 3);
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
