// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
  covergroup cg_with_sample(int init) with function sample (int addr, bit is_read);
  endgroup

  cg_with_sample cov1 = new(0);

  function void run();
    // Too few arguments (1 instead of 2)
    cov1.sample(1);
  endfunction
endmodule
