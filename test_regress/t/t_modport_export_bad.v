// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test error cases for modport export out-of-block definitions

interface bus_if;
  logic [7:0] data;

  modport provider(
    output data,
    export task send(input logic [7:0] val)
  );
endinterface

module driver(bus_if.provider port, input logic clk);
  // Error: 'clk' is a plain wire port, not an interface port
  task clk.send(input logic [7:0] val);
    port.data = val;
  endtask
endmodule

module t;
  bus_if bif();
  logic clk;
  driver drv(.port(bif.provider), .clk(clk));
endmodule
