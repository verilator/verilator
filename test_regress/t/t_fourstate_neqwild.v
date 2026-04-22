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

  initial begin
    if ((f('b101) !=? f('b101)) !== 0) $stop;
    if ((f('b101) !=? f('b10x)) !== 0) $stop;
    if ((f('b101) !=? f('b1xz)) !== 0) $stop;
    if ((f('b101) !=? f('b10z)) !== 0) $stop;
    if ((f('b1z1) !=? f('b10z)) !== 'x) $stop;
    if ((f('b1xx) !=? f('b1xx)) !== 0) $stop;
    if ((f('b1x1) !=? f('b101)) !== 'x) $stop;
    if ((f('b1zz) !=? f('b1xz)) !== 0) $stop;
    if ((f('bz01) !=? f('b1zx)) !== 'x) $stop;
    if ((f('b001) !=? f('b1zx)) !== 1) $stop;
    if ((f('b001) !=? f('b111)) !== 1) $stop;
    if ((f('bx00) !=? f('bxz1)) !== 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
