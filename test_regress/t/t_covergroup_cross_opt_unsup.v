// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  covergroup cg;
    cp_a: coverpoint 1'b0 {bins b0 = {0}; bins b1 = {1};}
    cp_b: coverpoint 1'b0 {bins b0 = {0}; bins b1 = {1};}
    cross_ab: cross cp_a, cp_b{
      option.per_instance = 1;  // unsupported for cross; triggers COVERIGN
    }
    cross_implicit: cross cp_a, var_x;
    // Non-standard hierarchical/dotted cross item: can only be a data reference
    // (implicit coverpoint), never a coverpoint.  Accepted with a NONSTD warning;
    // implicit coverpoints are unsupported so the cross is dropped (COVERIGN).
    cross_hier: cross cp_a, s_cfg.m_p;
  endgroup
  typedef struct packed {logic m_p; logic h_mode;} cfg_t;
  cfg_t s_cfg = '0;
  logic var_x = 1'b0;
  cg cg_i = new;
  initial begin
    cg_i.sample();
    $finish;
  end
endmodule
