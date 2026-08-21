// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class BaseState;
endclass

class DerivedState extends BaseState;
endclass

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

module CovergroupPortTypeMismatch(ModportIf.monitor intf);
  covergroup cg(input virtual ModportIf.driver vif);
    cp: coverpoint vif.value;
  endgroup

  cg cov = new(intf);
endmodule

module t;
  ParameterizedIf #(5) if5();
  ParameterizedIf #(6) if6();
  ModportIf modport_if();
  CovergroupPortTypeMismatch port_type_mismatch(modport_if);

  DerivedState derived_state = new;
  virtual ParameterizedIf #(5).monitor monitor_vif = if5;
  virtual ParameterizedIf #(6) vif6 = if6;
  virtual ParameterizedIf #(5).driver driver5[2];
  virtual ParameterizedIf #(6).monitor monitor6[2];
  bit mutable_value;

  function automatic bit mutate(ref bit value);
    value = 1;
    return value;
  endfunction

  covergroup cg_const_ref_type(const ref BaseState state);
    cp: coverpoint (state == null);
  endgroup

  covergroup cg_interface_types(input virtual ParameterizedIf #(5) input_vif,
                                ref virtual ParameterizedIf #(5) ref_vif,
                                const ref virtual ParameterizedIf #(5) const_ref_vif);
    cp: coverpoint input_vif.value;
  endgroup

  covergroup cg_read_only_ref(ref bit value);
    cp: coverpoint mutate(value);
  endgroup

  covergroup cg_array_input(input virtual ParameterizedIf #(5).monitor vifs[2]);
    cp: coverpoint vifs[0].value;
  endgroup

  covergroup cg_array_ref(ref virtual ParameterizedIf #(5).monitor vifs[2]);
    cp: coverpoint vifs[0].value;
  endgroup

  covergroup cg_array_const_ref(const ref virtual ParameterizedIf #(5).monitor vifs[2]);
    cp: coverpoint vifs[0].value;
  endgroup

  cg_const_ref_type const_ref_type_cg = new(derived_state);
  cg_interface_types interface_types_cg = new(vif6, vif6, vif6);
  cg_interface_types interface_modport_types_cg
      = new(monitor_vif, monitor_vif, monitor_vif);
  cg_read_only_ref read_only_ref_cg = new(mutable_value);
  cg_array_input bad_input_modport = new(driver5);
  cg_array_input bad_input_parameter = new(monitor6);
  cg_array_ref bad_ref_modport = new(driver5);
  cg_array_const_ref bad_const_ref_parameter = new(monitor6);
endmodule
