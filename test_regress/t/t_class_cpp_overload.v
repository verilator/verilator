// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface irq_if (
    input logic clk,
    input logic resetn
);
  logic irq;
  logic te;
  logic halted;
  logic fault;
  logic wfi;
  clocking cb @(posedge clk);
    default input #1step output #2ns;
    output irq;
    output te;
    input halted;
    input fault;
    input wfi;
  endclocking
  modport DUT_IRQ_PORT(input clk, resetn, output halted, fault, wfi);
endinterface
class base_test_class;
  function int foo();
  endfunction
  virtual irq_if.DUT_IRQ_PORT irq_vif;
  function new(string name);
  endfunction
  virtual function void build_phase();
    if (irq_vif == null) begin
      if (foo()) $display();
    end
  endfunction
endclass
module tb_top;
endmodule
