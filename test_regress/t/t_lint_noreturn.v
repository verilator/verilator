// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  // verilator lint_off UNDRIVEN

  function int no_rtn();  // <--- Warning: No return
  endfunction

  int i;

  initial begin
    i = no_rtn();
    if (i !== 0) $stop;
    $finish;
  end

endmodule
