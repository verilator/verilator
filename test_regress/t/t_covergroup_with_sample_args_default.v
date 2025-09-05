// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
  covergroup cg_with_sample(int init) with function sample (int addr, bit is_read = 1'b0);
  endgroup

  cg_with_sample cov1 = new(7);

  function void run();
    cov1.sample(5);
    cov1.sample(6, 1'b1);
  endfunction
endmodule
