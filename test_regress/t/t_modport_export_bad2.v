// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test error: out-of-block task with no matching export prototype

interface bus_if;
  logic [7:0] data;

  modport provider(
    output data
    // No export prototype for 'send'
  );
endinterface

module driver(bus_if.provider port);
  // Error: no export prototype for 'send' in interface
  task port.send(input logic [7:0] val);
    port.data = val;
  endtask
endmodule

module t;
  bus_if bif();
  driver drv(.port(bif.provider));
endmodule
