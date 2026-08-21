// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// A plain (non-covergroup) class included to verify it does not interfere with covergroup handling
class PlainClass;
    int x;
endclass

class CoverageState;
  bit test;
  bit enable;
endclass

class ParameterizedCoverageState #(int WIDTH = 5);
  bit [WIDTH-1:0] value;
  bit enable;
endclass

interface BasicCoverageIf;
  logic value;
  logic enable;
  modport monitor(input value, enable);
endinterface

interface ParameterizedCoverageIf #(int WIDTH = 5);
  logic [WIDTH-1:0] value;
  logic enable;
  modport monitor(input value, enable);
endinterface

module CoverageInterfacePort(BasicCoverageIf basic_port,
                             ParameterizedCoverageIf param_port);
  covergroup cg_port(input virtual BasicCoverageIf basic_unqualified,
                     input virtual BasicCoverageIf.monitor basic_qualified,
                     input virtual ParameterizedCoverageIf #(5) param_unqualified,
                     input virtual ParameterizedCoverageIf #(5).monitor param_qualified);
    cp_basic_unqualified: coverpoint basic_unqualified.value {
      bins zero = {0};
      bins one = {1};
    }
    cp_basic_qualified: coverpoint basic_qualified.value {
      bins zero = {0};
      bins one = {1};
    }
    cp_param_unqualified: coverpoint param_unqualified.value {
      bins zero = {0};
      bins one = {1};
    }
    cp_param_qualified: coverpoint param_qualified.value {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  cg_port cov;

  initial begin
    cov = new(basic_port, basic_port, param_port, param_port);
    cov.sample();
  end
endmodule

typedef struct packed {
  bit flag;
  bit [2:0] value;
} PackedCoverageState;

class Coverage;
  covergroup cg(CoverageState st);
    cp_test: coverpoint st.test {
      bins zero = {0};
      bins one = {1};
    }
    cp_iff: coverpoint st.test iff (st.enable) {
      bins one = {1};
    }
  endgroup
  CoverageState state;
  function new();
    state = new();
    cg = new(state);
  endfunction
endclass

class CoverageExplicitInput;
  covergroup explicit_cg(input CoverageState st);
    cp_explicit: coverpoint st.test {
      bins zero = {0};
      bins one = {1};
    }
  endgroup
  CoverageState state;
  function new();
    state = new();
    explicit_cg = new(state);
  endfunction
endclass

class CoverageParent;
  CoverageState state;
  function new();
    state = new();
  endfunction
endclass

class CoverageFromParent extends CoverageParent;
  covergroup parent_cg(CoverageState st);
    cp_parent: coverpoint st.test {
      bins zero = {0};
      bins one = {1};
    }
  endgroup
  function new();
    super.new();
    parent_cg = new(state);
  endfunction
endclass

class CoverageRefFromParent extends CoverageParent;
  covergroup parent_ref_cg(ref CoverageState st);
    cp_parent_ref: coverpoint st.test iff (st.enable) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup
  function new();
    super.new();
    state.enable = 1;
    parent_ref_cg = new(state);
  endfunction
endclass

class CoverageMixed;
  bit [3:0] local_value;
  CoverageState state;
  covergroup mixed_cg(CoverageState st);
    cp_sum: coverpoint local_value + st.test {
      bins two = {2};
      bins three = {3};
    }
  endgroup
  function new();
    local_value = 2;
    state = new();
    mixed_cg = new(state);
  endfunction
endclass

// Top-level (file-scope) covergroup declared outside any module
covergroup cg_toplevel;
  cp_tl: coverpoint 0;
endgroup

module t;

  BasicCoverageIf basic_if_a();
  BasicCoverageIf basic_if_b();
  BasicCoverageIf basic_if_port();
  ParameterizedCoverageIf #(5) param_if_a();
  ParameterizedCoverageIf #(5) param_if_b();
  ParameterizedCoverageIf #(5) param_if_port();
  CoverageInterfacePort interface_port_cov(basic_if_port, param_if_port);

  int i, j;
  logic clk = 0;
  CoverageState global_state = new;
  CoverageState global_original = global_state;
  CoverageState first_state = new;
  CoverageState second_state = new;
  CoverageState named_first_state = new;
  CoverageState named_second_state = new;
  CoverageState ref_state = new;
  CoverageState const_ref_state = new;
  CoverageState mixed_ref_state = new;
  bit ref_value;
  bit ref_enable = 1;
  bit const_ref_value;
  bit const_ref_enable = 1;
  bit mixed_ref_value;
  bit [1:0] mixed_ref_bias;
  PackedCoverageState ref_struct;
  bit [3:0] ref_array[2];
  bit [95:0] ref_wide;
  CoverageState ref_compare_state = new;
  ParameterizedCoverageState #(5) param_input_state;
  ParameterizedCoverageState #(5) param_input_original;
  ParameterizedCoverageState #(5) param_ref_state;
  ParameterizedCoverageState #(5) param_const_ref_state;
  virtual BasicCoverageIf basic_input_vif;
`ifdef VERILATOR
  virtual ParameterizedCoverageIf #(5).monitor param_array_vifs[2];
  virtual ParameterizedCoverageIf #(5).monitor param_array_vifs_2d[2][3];
  virtual ParameterizedCoverageIf #(5).monitor param_array_vifs_shifted[3:2];
`endif
  virtual ParameterizedCoverageIf #(5).monitor param_ref_vif;
  virtual ParameterizedCoverageIf #(5).monitor param_const_ref_vif;

  function automatic bit wide_ref_bit(const ref bit [95:0] value);
    // verilator no_inline_task
    return value[80];
  endfunction

  covergroup cg(int var1, int var2 = 42);
    cp1: coverpoint i { bins lo = {[0:4]}; bins hi = {[5:9]}; }
  endgroup

  covergroup cg_global(CoverageState st);
    cp_global: coverpoint st.test {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_multiple(CoverageState first, CoverageState second);
    cp_first: coverpoint first.test {
      bins zero = {0};
      bins one = {1};
    }
    cp_second: coverpoint second.test {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_ref_scalar(ref bit value, ref bit enabled);
    cp_ref_scalar: coverpoint value iff (enabled) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_const_ref_scalar(const ref bit value, const ref bit enabled);
    cp_const_ref_scalar: coverpoint value iff (enabled) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_ref_handle(ref CoverageState st);
    cp_ref_handle: coverpoint st.test iff (st.enable) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_const_ref_handle(const ref CoverageState st);
    cp_const_ref_handle: coverpoint st.test iff (st.enable) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_mixed_refs(input bit [1:0] bias, ref bit value, const ref CoverageState st);
    cp_mixed_refs: coverpoint bias + value iff (st.enable) {
      bins one = {1};
      bins two = {2};
    }
  endgroup

  covergroup cg_ref_types(ref PackedCoverageState state, ref bit [3:0] values[2],
                          ref bit [95:0] wide_value, const ref CoverageState handle);
    cp_struct: coverpoint state.value {
      bins zero = {0};
      bins one = {1};
    }
    cp_array: coverpoint values[1] {
      bins zero = {0};
      bins one = {1};
    }
    cp_wide: coverpoint wide_value[80] {
      bins zero = {0};
      bins one = {1};
    }
    cp_wide_helper: coverpoint wide_ref_bit(wide_value) {
      bins zero = {0};
      bins one = {1};
    }
    cp_handle_compare: coverpoint (handle == null) {
      bins nonnull = {0};
      bins isnull = {1};
    }
  endgroup

  covergroup cg_param_class(input ParameterizedCoverageState #(5) input_state,
                            ref ParameterizedCoverageState #(5) ref_state,
                            const ref ParameterizedCoverageState #(5) const_ref_state);
    cp_param_input: coverpoint input_state.value {
      bins zero = {0};
      bins one = {1};
    }
    cp_param_ref: coverpoint ref_state.value iff (ref_state.enable) {
      bins zero = {0};
      bins one = {1};
    }
    cp_param_const_ref: coverpoint const_ref_state.value iff (const_ref_state.enable) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_interfaces(input virtual BasicCoverageIf.monitor input_vif,
                           ref virtual ParameterizedCoverageIf #(5).monitor ref_vif,
                           const ref virtual ParameterizedCoverageIf #(5).monitor const_ref_vif);
    cp_basic_input: coverpoint input_vif.value iff (input_vif.enable) {
      bins zero = {0};
      bins one = {1};
    }
    cp_param_ref: coverpoint ref_vif.value iff (ref_vif.enable) {
      bins zero = {0};
      bins one = {1};
    }
    cp_param_const_ref: coverpoint const_ref_vif.value iff (const_ref_vif.enable) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_interfaces_unqualified(input virtual BasicCoverageIf basic_vif,
                                       input virtual ParameterizedCoverageIf #(5) param_vif);
    cp_basic: coverpoint basic_vif.value {
      bins zero = {0};
      bins one = {1};
    }
    cp_param: coverpoint param_vif.value {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

`ifdef VERILATOR
  // Commercial simulator support is mixed, some report virtual-interface array covergroup
  // arguments as not yet implemented and Questa crashes.
  covergroup cg_interface_arrays(
      input virtual ParameterizedCoverageIf #(5).monitor input_vifs[2],
      ref virtual ParameterizedCoverageIf #(5).monitor ref_vifs[2],
      const ref virtual ParameterizedCoverageIf #(5).monitor const_ref_vifs[2],
      ref virtual ParameterizedCoverageIf #(5).monitor ref_vifs_2d[2][3]);
    cp_input: coverpoint input_vifs[0].value {
      bins zero = {0};
      bins one = {1};
    }
    cp_ref: coverpoint ref_vifs[0].value {
      bins zero = {0};
      bins one = {1};
    }
    cp_const_ref: coverpoint const_ref_vifs[0].value {
      bins zero = {0};
      bins one = {1};
    }
    cp_ref_2d: coverpoint ref_vifs_2d[0][0].value {
      bins zero = {0};
      bins one = {1};
    }
  endgroup
`endif

  covergroup cg_sample_inputs with function sample(input bit value, input CoverageState st);
    cp_sample_inputs: coverpoint value iff (st.enable) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_sample_param_class with function sample(
      input ParameterizedCoverageState #(5) first_state,
      input ParameterizedCoverageState #(5) second_state);
    cp_first: coverpoint first_state.value iff (first_state.enable) {
      bins zero = {0};
      bins one = {1};
    }
    cp_second: coverpoint second_state.value iff (second_state.enable) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  covergroup cg_sample_interfaces with function sample(
      input virtual BasicCoverageIf basic_vif,
      input virtual ParameterizedCoverageIf #(5).monitor param_vif);
    cp_basic_input: coverpoint basic_vif.value iff (basic_vif.enable) {
      bins zero = {0};
      bins one = {1};
    }
    cp_param_input: coverpoint param_vif.value iff (param_vif.enable) {
      bins zero = {0};
      bins one = {1};
    }
  endgroup

  // Clocked covergroup with constructor arguments
  covergroup cg_clocked(int lim) @(posedge clk);
    cp_clocked: coverpoint i { bins lo = {[0:4]}; bins hi = {[5:9]}; }
  endgroup

  // 'with function sample' covergroup whose coverpoint references its own sample-argument
  // member.  That reference resolves to a member of the covergroup class itself and so must
  // NOT be mistaken for an unsupported enclosing-class reference (and skipped).
  covergroup cg_samp with function sample(bit [1:0] x);
    cp: coverpoint x { bins b0 = {0}; bins b3 = {3}; }
  endgroup

  covergroup cg_cross_iff with function sample(bit a, bit b, bit enable_a, bit enable_b);
    cp_a: coverpoint a iff (enable_a) { bins one = {1}; }
    cp_b: coverpoint b iff (enable_b) { bins one = {1}; }
    cross_ab: cross cp_a, cp_b;
  endgroup

  cg cov1 = new(69, 77);
  cg cov2 = new(69);
  cg_clocked cov_clocked = new(10);
  cg_samp cov_samp = new;
  cg_cross_iff cov_cross_iff = new;
  Coverage cov_handle = new;
  CoverageExplicitInput cov_explicit = new;
  CoverageFromParent cov_parent = new;
  CoverageRefFromParent cov_ref_parent = new;
  CoverageMixed cov_mixed = new;
  cg_global cov_global = new(global_state);
  cg_multiple cov_multiple = new(first_state, second_state);
  cg_multiple cov_named
      = new(.second(named_second_state), .first(named_first_state));
  cg_ref_scalar cov_ref_scalar = new(ref_value, ref_enable);
  cg_const_ref_scalar cov_const_ref_scalar = new(const_ref_value, const_ref_enable);
  cg_ref_handle cov_ref_handle = new(ref_state);
  cg_const_ref_handle cov_const_ref_handle = new(const_ref_state);
  cg_mixed_refs cov_mixed_refs;
  cg_ref_types cov_ref_types = new(ref_struct, ref_array, ref_wide, ref_compare_state);
  cg_param_class cov_param_class;
`ifdef VERILATOR
  cg_interface_arrays cov_interface_arrays;
  cg_interface_arrays cov_interface_arrays_shifted;
`endif
  cg_interfaces cov_interfaces;
  cg_interfaces_unqualified cov_interfaces_unqualified;
  cg_sample_inputs cov_sample_inputs = new;
  cg_sample_param_class cov_sample_param_class = new;
  cg_sample_interfaces cov_sample_interfaces = new;
  PlainClass plain_inst = new;  // Non-covergroup class instance - must not affect covergroup coverage

`ifdef VERILATOR
  function automatic void check_interface_array_args();
    cov_interface_arrays = new(
        param_array_vifs, param_array_vifs, param_array_vifs, param_array_vifs_2d);
    cov_interface_arrays_shifted = new(
        param_array_vifs, param_array_vifs_shifted, param_array_vifs, param_array_vifs_2d);
    cov_interface_arrays.sample();
    cov_interface_arrays_shifted.sample();
  endfunction
`endif

  function void x();
    real cov_result;
    cov1.set_inst_name("the_inst_name");
    cov1.start();
    cov1.sample();
    cov1.stop();

    cov_result = cov2.get_coverage();
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_coverage() out of range: %f", cov_result);

    cov_result = cov2.get_coverage(i, j);
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_coverage(i,j) return out of range: %f", cov_result);

    cov_result = cov2.get_inst_coverage();
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_inst_coverage() out of range: %f", cov_result);

    cov_result = cov2.get_inst_coverage(i, j);
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_inst_coverage(i,j) return out of range: %f", cov_result);

    cov_result = cg::get_coverage();
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: cg::get_coverage() out of range: %f", cov_result);

    cov_result = cg::get_coverage(i, j);
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: cg::get_coverage(i,j) return out of range: %f", cov_result);
  endfunction

  initial begin
    param_input_state = new;
    param_input_original = param_input_state;
    param_ref_state = new;
    param_ref_state.enable = 1;
    param_const_ref_state = new;
    param_const_ref_state.enable = 1;
    cov_param_class = new(param_input_state, param_ref_state, param_const_ref_state);
    basic_input_vif = basic_if_a;
    param_ref_vif = param_if_a;
    param_const_ref_vif = param_if_a;
`ifdef VERILATOR
    param_array_vifs[0] = param_if_a;
    param_array_vifs[1] = param_if_b;
    param_array_vifs_2d[0][0] = param_if_a;
    param_array_vifs_shifted[3] = param_if_a;
    param_array_vifs_shifted[2] = param_if_b;
`endif
    basic_if_a.enable = 1;
    basic_if_b.enable = 1;
    param_if_a.enable = 1;
    param_if_b.enable = 1;
    cov_interfaces = new(basic_input_vif, param_ref_vif, param_const_ref_vif);
    cov_interfaces_unqualified = new(basic_if_a, param_if_a);
`ifdef VERILATOR
    check_interface_array_args();
`endif
    mixed_ref_bias = 1;
    cov_mixed_refs
        = new(.st(mixed_ref_state), .value(mixed_ref_value), .bias(mixed_ref_bias));
    i = 3;
    x();  // samples cov1 with i=3 -> lo bin hit
    clk = 1;  // posedge: samples cov_clocked with i=3 -> lo bin hit
    // Sample-arg coverpoint: the passed value must reach the coverpoint.  Sampling 0 then 3
    // must hit b0 and b3 respectively; if the argument were dropped (member left at its
    // default 0) b3 would never be hit.
    cov_samp.sample(2'd0);
    cov_samp.sample(2'd3);
    cov_cross_iff.sample(1, 1, 0, 1);
    cov_cross_iff.sample(1, 1, 1, 0);
    cov_cross_iff.sample(1, 1, 1, 1);
    cov_handle.cg.sample();
    cov_handle.state.test = 1;
    cov_handle.state.enable = 1;
    cov_handle.cg.sample();
    cov_explicit.explicit_cg.sample();
    cov_explicit.state.test = 1;
    cov_explicit.explicit_cg.sample();
    cov_parent.parent_cg.sample();
    cov_parent.state.test = 1;
    cov_parent.parent_cg.sample();
    cov_ref_parent.parent_ref_cg.sample();
    cov_ref_parent.state = new;
    cov_ref_parent.state.enable = 1;
    cov_ref_parent.state.test = 1;
    cov_ref_parent.parent_ref_cg.sample();
    cov_mixed.mixed_cg.sample();
    cov_mixed.state.test = 1;
    cov_mixed.mixed_cg.sample();
    cov_global.sample();
    global_state = new;
    global_state.test = 1;
    cov_global.sample();
    global_original.test = 1;
    cov_global.sample();
    second_state.test = 1;
    cov_multiple.sample();
    first_state.test = 1;
    second_state.test = 0;
    cov_multiple.sample();
    named_second_state.test = 1;
    cov_named.sample();
    named_first_state.test = 1;
    named_second_state.test = 0;
    cov_named.sample();
    cov_ref_scalar.sample();
    ref_value = 1;
    cov_ref_scalar.sample();
    ref_enable = 0;
    ref_value = 0;
    cov_ref_scalar.sample();
    cov_const_ref_scalar.sample();
    const_ref_value = 1;
    cov_const_ref_scalar.sample();
    const_ref_enable = 0;
    const_ref_value = 0;
    cov_const_ref_scalar.sample();
    ref_state.enable = 1;
    cov_ref_handle.sample();
    ref_state = new;
    ref_state.enable = 1;
    ref_state.test = 1;
    cov_ref_handle.sample();
    const_ref_state.enable = 1;
    cov_const_ref_handle.sample();
    const_ref_state = new;
    const_ref_state.enable = 1;
    const_ref_state.test = 1;
    cov_const_ref_handle.sample();
    mixed_ref_state.enable = 1;
    cov_mixed_refs.sample();
    mixed_ref_bias = 0;
    mixed_ref_value = 1;
    cov_mixed_refs.sample();
    mixed_ref_value = 0;
    cov_mixed_refs.sample();
    cov_ref_types.sample();
    ref_struct.value = 1;
    ref_array[1] = 1;
    ref_wide[80] = 1;
    ref_compare_state = null;
    cov_ref_types.sample();
    cov_param_class.sample();
    param_input_state = new;
    param_input_state.value = 1;
    param_ref_state = new;
    param_ref_state.enable = 1;
    param_ref_state.value = 1;
    param_const_ref_state = new;
    param_const_ref_state.enable = 1;
    param_const_ref_state.value = 1;
    cov_param_class.sample();
    param_input_original.value = 1;
    cov_param_class.sample();
    cov_interfaces.sample();
    cov_interfaces_unqualified.sample();
    basic_input_vif = basic_if_b;
    basic_if_b.value = 1;
    param_ref_vif = param_if_b;
    param_const_ref_vif = param_if_b;
    param_if_b.value = 1;
    cov_interfaces.sample();
    cov_interfaces_unqualified.sample();
    basic_if_a.value = 1;
    cov_interfaces.sample();
    cov_interfaces_unqualified.sample();
    ref_compare_state = new;
    ref_compare_state.enable = 1;
    cov_sample_inputs.sample(ref_value, ref_compare_state);
    ref_value = 1;
    cov_sample_inputs.sample(ref_value, ref_compare_state);
    cov_sample_param_class.sample(param_ref_state, param_const_ref_state);
    param_ref_state.value = 0;
    param_const_ref_state.value = 0;
    cov_sample_param_class.sample(param_ref_state, param_const_ref_state);
    cov_sample_interfaces.sample(basic_input_vif, param_ref_vif);
    basic_if_b.value = 0;
    param_if_b.value = 0;
    cov_sample_interfaces.sample(basic_input_vif, param_ref_vif);
    $finish;
  end

endmodule
