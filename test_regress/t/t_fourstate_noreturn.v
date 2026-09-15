// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  function logic foo();
    $c(";");
  endfunction
  function logic bar();
  endfunction

  initial begin
    if (foo() !== 'x) $stop;
    if (bar() !== 'x) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
