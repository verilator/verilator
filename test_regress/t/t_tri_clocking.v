// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface wb_ifc;
  logic clk;
  wire rst;
  tri0 cyc;
  clocking mck @(posedge clk);
    input rst;
    output cyc;
  endclocking
endinterface

module t;
  wb_ifc wb_ma ();
  initial $finish;
endmodule
