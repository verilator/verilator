// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  function automatic bit function_ref(ref bit value);
    return value;
  endfunction

  function automatic bit function_output(output bit value);
    value = 1;
    return value;
  endfunction

  covergroup cg with function sample(bit value);
    cp_option: coverpoint value {
      bins ref_bin = {0, function_ref(value)};
      bins output_bin = {function_output(value)};
      option.at_least = value;
    }
  endgroup

  covergroup cg_constructor_ref(ref bit value);
    cp_constructor_ref: coverpoint value {
      bins bad = {value};
    }
  endgroup

  bit nonconstant_bound;
  covergroup cg_cross_bad;
    cp_bad: coverpoint 0 iff (1) {
      bins bad = {[0:nonconstant_bound]};
    }
    cp_ok: coverpoint 0 { bins zero = {0}; }
    cross_bad: cross cp_bad, cp_ok;
  endgroup

  cg cov = new;
  bit constructor_value;
  cg_constructor_ref constructor_cov = new(constructor_value);
  cg_cross_bad cross_bad_cov = new;
endmodule
