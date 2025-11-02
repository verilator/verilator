// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
  covergroup cg0 with function sample ();
  endgroup
  cg0 cov = new();
  function void run();
    cov.sample();
  endfunction
endmodule
