// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
  covergroup cgN with function sample (int addr, bit is_read);
  endgroup
  cgN cov = new();
  function void run();
    cov.sample(.addr(11), .is_read(1'b1));
  endfunction
endmodule
