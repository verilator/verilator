// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit value;

  covergroup cg_ref(ref bit arg = value);
    cp: coverpoint arg;
  endgroup

  covergroup cg_const_ref(const ref bit arg = value);
    cp: coverpoint arg;
  endgroup

  cg_ref ref_cg = new;
  cg_const_ref const_ref_cg = new;
endmodule
