// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  function integer foo(integer a, integer b);
    return a + b;
  endfunction

  initial begin
    static logic v = 'x;
    $write("%d\n", v);
    v = 'z;
    $write("%d\n", v);
    v = 0;
    $write("%d\n", v);
    v = 1;
    $write("%d\n", v);
    $write("%d\n", foo(1, 2));
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
