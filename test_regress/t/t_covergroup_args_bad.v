// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit value;

  covergroup cg_output(output bit arg);
    cp: coverpoint arg;
  endgroup

  covergroup cg_inout(inout bit arg);
    cp: coverpoint arg;
  endgroup

  covergroup cg_sample_output with function sample(output bit arg);
    cp: coverpoint arg;
  endgroup

  covergroup cg_sample_inout with function sample(inout bit arg);
    cp: coverpoint arg;
  endgroup

  covergroup cg_sample_ref with function sample(ref bit arg);
    cp: coverpoint arg;
  endgroup

  covergroup cg_sample_const_ref with function sample(const ref bit arg);
    cp: coverpoint arg;
  endgroup

  covergroup cg_duplicate(bit arg) with function sample(bit arg);
    cp: coverpoint arg;
  endgroup

  cg_output output_cg = new(value);
  cg_inout inout_cg = new(value);
  cg_sample_output sample_output_cg = new;
  cg_sample_inout sample_inout_cg = new;
  cg_sample_ref sample_ref_cg = new;
  cg_sample_const_ref sample_const_ref_cg = new;
  cg_duplicate duplicate_cg = new(value);
endmodule
