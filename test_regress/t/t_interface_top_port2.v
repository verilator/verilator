// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkb(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0b exp=%0b (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface virt_if;
  logic v;
endinterface

interface inner_if;
  logic a;
  virtual virt_if vif;
endinterface

interface outer_if (
    input logic clk
);
  logic a;
  inner_if inner();
  always_ff @(posedge clk) begin
    if (a) inner.a = 1'b1;
    else inner.a = 1'b0;
  end
endinterface

module t (
    outer_if outer
);
  virt_if vif_inst();
  initial begin
    vif_inst.v = 1'b0;
    outer.inner.vif = vif_inst;
    outer.inner.vif.v = 1'b1;
    `checkb(vif_inst.v, 1'b1);
  end
endmodule
