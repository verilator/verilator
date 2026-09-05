// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  function logic f(logic a);
    if (a === 1'b1) $write("1");
    else if (a === 1'b0) $write("0");
    else if (a === 1'bx) $write("x");
    else if (a === 1'bz) $write("z");
    else $stop;
    $write("\n");
    return a;
  endfunction

  initial begin
    if ((f(0) && f(0)) !== 0) $stop;
    if ((f(0) && f(1)) !== 0) $stop;
    if ((f(0) && f('x)) !== 0) $stop;
    if ((f(0) && f('z)) !== 0) $stop;

    if ((f(1) && f(0)) !== 0) $stop;
    if ((f(1) && f(1)) !== 1) $stop;
    if ((f(1) && f('x)) !== 'x) $stop;
    if ((f(1) && f('z)) !== 'x) $stop;

    if ((f('x) && f(0)) !== 0) $stop;
    if ((f('x) && f(1)) !== 'x) $stop;
    if ((f('x) && f('x)) !== 'x) $stop;
    if ((f('x) && f('z)) !== 'x) $stop;

    if ((f('z) && f(0)) !== 0) $stop;
    if ((f('z) && f(1)) !== 'x) $stop;
    if ((f('z) && f('x)) !== 'x) $stop;
    if ((f('z) && f('z)) !== 'x) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
