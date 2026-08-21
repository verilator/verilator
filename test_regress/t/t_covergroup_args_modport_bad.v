// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ParameterizedIf #(int WIDTH = 5);
  logic [WIDTH-1:0] value;
  modport monitor(input value);
  modport driver(output value);
endinterface

interface ModportIf;
  logic value;
  modport monitor(input value);
  modport driver(output value);
endinterface

module PortTypeMismatch(ModportIf.monitor intf);
  covergroup cg(input virtual ModportIf.driver vif);
    cp: coverpoint vif.value;
  endgroup

  cg cov = new(intf);
endmodule

module t;
  ParameterizedIf #(5) intf();
  ModportIf modport_intf();
  PortTypeMismatch port_type_mismatch(modport_intf);
  virtual interface ParameterizedIf #(5).monitor monitor_vif = intf;

  covergroup cg(input virtual ParameterizedIf #(5) input_vif,
                ref virtual ParameterizedIf #(5) ref_vif,
                const ref virtual ParameterizedIf #(5) const_ref_vif);
    cp: coverpoint input_vif.value;
  endgroup

  cg cov = new(monitor_vif, monitor_vif, monitor_vif);
endmodule
