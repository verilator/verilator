// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int values[$] = '{1, 2};

  covergroup cg with function sample (int value);
    cp: coverpoint value {
      bins sized[2] = values;
      bins missing_brackets = values;
    }
  endgroup

  cg cg_inst = new;
endmodule
