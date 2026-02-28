// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
  covergroup cg_with_sample(int init_val) with function sample (int addr, bit is_read);
  endgroup

  cg_with_sample cov1 = new(42);

  function void run();
    cov1.sample(16, 1'b1);
  endfunction
endmodule
