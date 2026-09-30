// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// type_option.merge_instances is a type option, so constant (IEEE 1800-2023 19.7.1)

module t;
  bit a;

  covergroup cg(bit merge);
    type_option.merge_instances = merge;  // <--- Bad: not constant
    cp: coverpoint a;
  endgroup

  cg c = new(1);
endmodule
