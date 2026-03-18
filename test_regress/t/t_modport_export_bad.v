// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

interface bus_if;
  logic [7:0] data;

  modport provider(
    output data,
    export task send(input logic [7:0] val)
  );
endinterface

// Error 1: 'clk' is a plain wire port, not an interface port
module driver1(bus_if.provider port, input logic clk);
  task clk.send(input logic [7:0] val);  // lint_off: UNUSED
    port.data = val;
  endtask
endmodule

// Error 2: 'nonexistent' is not a port on this module
module driver2(bus_if.provider port);
  task nonexistent.send(input logic [7:0] val);
    port.data = val;
  endtask
endmodule

interface bus_if_noexport;
  logic [7:0] data;

  modport provider(
    output data
  );
endinterface

// Error 3: no export prototype for 'send' in interface
module driver3(bus_if_noexport.provider port);
  task port.send(input logic [7:0] val);
    port.data = val;
  endtask
endmodule

module t;
  bus_if bif();
  logic clk;
  driver1 drv1(.port(bif.provider), .clk(clk));
  driver2 drv2(.port(bif.provider));
  bus_if_noexport bif2();
  driver3 drv3(.port(bif2.provider));
endmodule
