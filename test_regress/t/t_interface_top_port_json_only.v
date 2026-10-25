// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inner_ifc;
  logic inner_value;
endinterface

interface ifc (
    input logic clk
);
  logic [4:0] value;
  logic reset;
  inner_ifc iifc();
  modport counter_mp(input clk, input reset, output value);
  modport core_mp(input clk, output reset, input value);
endinterface

module t (
    ifc if_port,
    ifc if_port_array[6:5][2:4],
    ifc.counter_mp mod_port1,
    ifc.core_mp mod_port2
);
endmodule
