// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  function int f;
    fork
      ;
    join_any  // Illegal 13.4.4
    return 0;
  endfunction

  int i;

  initial begin
    i = f();
  end

endmodule
