// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package s_core_env_pkg;
  virtual class x_scoreboard;
    extern function void has_ext_ok();
  endclass
  function void x_scoreboard::has_ext_ok();
  endfunction

  class cls_misses_new_1 extends x_scoreboard;
    extern function new();  // <--- BAD
  endclass

endpackage

module t;
endmodule
