// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface Iface;
  logic clk = 1'b0, out = 1'b0;
  clocking cb @(posedge clk);
    output out;
  endclocking
endinterface

module t;
  logic data[];
  Iface mod0 ();
  virtual Iface mod1 = mod0;

  initial begin
    mod1.cb.out <= 1'b1;
    // Bad - unpacked array driven onto a scalar clockvar
    mod1.cb.out <= data;
  end
endmodule
