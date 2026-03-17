// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test error: out-of-block task referencing non-existent port

interface bus_if;
  logic [7:0] data;

  modport provider(
    output data,
    export task send(input logic [7:0] val)
  );
endinterface

module driver(bus_if.provider port);
  // Error: 'nonexistent' is not a port on this module
  task nonexistent.send(input logic [7:0] val);
    port.data = val;
  endtask
endmodule

module t;
  bus_if bif();
  driver drv(.port(bif.provider));
endmodule
