// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Hyeonuk Jeong
// SPDX-License-Identifier: CC0-1.0

module t;
  int value;
  covergroup cg;
    cp: coverpoint value;
  endgroup
  cg inst = new;
endmodule
