// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`ifdef VERILATOR
`define IMPURE_ONE ($c(1))
`else
`define IMPURE_ONE (|($random | $random))
`endif

module t;
  function integer f(integer x);
    if (`IMPURE_ONE) return x;
    return 'x;
  endfunction
  function logic [31:0] g(logic [31:0] x);
    if (`IMPURE_ONE) return x;
    return 'x;
  endfunction

  initial begin
    if ((f(10) + f(-5)) !== 5) $stop;
    if ((f(10) + f('b11x)) !== 'x) $stop;
    if ((f(10) + f('b11z)) !== 'x) $stop;
    if ((g(10) + g(5)) !== 15) $stop;
    if ((g(10) + g('x)) !== 'x) $stop;

    if ((f(10) - f(-5)) !== 15) $stop;
    if ((f(10) - f('b11x)) !== 'x) $stop;
    if ((f(10) - f('b11z)) !== 'x) $stop;
    if ((g(10) - g(5)) !== 5) $stop;
    if ((g(10) - g('x)) !== 'x) $stop;

    if ((f(10) * f(-5)) !== -50) $stop;
    if ((f(10) * f('b11x)) !== 'x) $stop;
    if ((f(10) * f('b11z)) !== 'x) $stop;
    if ((g(10) * g(5)) !== 50) $stop;
    if ((g(10) * g('x)) !== 'x) $stop;

    if ((f(10) / f(5)) !== 2) $stop;
    if ((f(9) / f(5)) !== 1) $stop;
    if ((f(10) / f(2)) !== 5) $stop;
    if ((f(-10) / f(5)) !== -2) $stop;
    if ((f(9) / f(-5)) !== -1) $stop;
    if ((f('bx) / f('bx)) !== 'x) $stop;
    if ((f('bz) / f(5)) !== 'x) $stop;
    if ((f(10) / f(0)) !== 'x) $stop;
    if ((f(0) / f(0)) !== 'x) $stop;
    if ((f(0) / f('z)) !== 'x) $stop;

    if ((g(10) / g(5)) !== 2) $stop;
    if ((g(9) / g(5)) !== 1) $stop;
    if ((g(10) / g(2)) !== 5) $stop;
    if ((g('bx) / g('bx)) !== 'x) $stop;
    if ((g('bz) / g(5)) !== 'x) $stop;
    if ((g(10) / g(0)) !== 'x) $stop;
    if ((g(0) / g(0)) !== 'x) $stop;
    if ((g(0) / g('z)) !== 'x) $stop;

    if ((f(10) % f(5)) !== 0) $stop;
    if ((f(9) % f(5)) !== 4) $stop;
    if ((f(10) % f(2)) !== 0) $stop;
    if ((f(-10) % f(5)) !== 0) $stop;
    if ((f(9) % f(-5)) !== 4) $stop;
    if ((f('bx) % f('bx)) !== 'x) $stop;
    if ((f('bz) % f(5)) !== 'x) $stop;
    if ((f(10) % f(0)) !== 'x) $stop;
    if ((f(0) % f(0)) !== 'x) $stop;
    if ((f(0) % f('z)) !== 'x) $stop;

    if ((g(10) % g(5)) !== 0) $stop;
    if ((g(9) % g(5)) !== 4) $stop;
    if ((g(10) % g(2)) !== 0) $stop;
    if ((g('bx) % g('bx)) !== 'x) $stop;
    if ((g('bz) % g(5)) !== 'x) $stop;
    if ((g(10) % g(0)) !== 'x) $stop;
    if ((g(0) % g(0)) !== 'x) $stop;
    if ((g(0) % g('z)) !== 'x) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
