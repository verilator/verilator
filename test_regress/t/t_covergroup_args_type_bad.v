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
endinterface

module t;
  ParameterizedIf #(6) if6();

  DerivedState derived_state = new;
  virtual ParameterizedIf #(6) vif6 = if6;
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

  cg_const_ref_type const_ref_type_cg = new(derived_state);
  cg_interface_types interface_types_cg = new(vif6, vif6, vif6);
  cg_read_only_ref read_only_ref_cg = new(mutable_value);
endmodule
