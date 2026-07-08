// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface iface_if #(
    parameter int W = 8
) (
    input bit clk
);
  logic [W-1:0] sig = 0;
  int passed = 0;
  assert property (@(posedge clk) s_eventually (sig == 1)) passed++;
endinterface

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;
  int cyc = 0;

  // Two distinct specializations: V3Param clones the interface into two
  // modules, each with its own s_eventually tracking. The generated final
  // block must stay per-module.
  iface_if #(.W(4)) a (.clk(clk));
  iface_if #(.W(8)) b (.clk(clk));

  always @(posedge clk) begin
    ++cyc;
    if (cyc == 2) begin
      a.sig <= 1;
      b.sig <= 1;
    end
    if (cyc == 5) begin
      if (a.passed == 0 || b.passed == 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
