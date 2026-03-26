// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  int a;
  int b;

  covergroup cg_cross_local_func_unsup;
    cross a, b {
      function void crossfunc;
      endfunction
      bins one = crossfunc();
    }
  endgroup

endmodule
