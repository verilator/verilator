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
    if ((f('b1) << f('b0)) !== 'b1) $stop;
    if ((f('b1) << f('b1)) !== 'b10) $stop;
    if ((f('b1) << f('b10)) !== 'b100) $stop;
    if ((f('b0x01) << f('b10)) !== 'b0x0100) $stop;
    if ((f('b0zx01) << f('b10)) !== 'b0zx0100) $stop;
    if ((f('b1) << f('b1x)) !== 'x) $stop;
    if ((f('b1) << f('b1z)) !== 'x) $stop;

    if ((f('b1) >> f('b0)) !== 'b1) $stop;
    if ((f('b10) >> f('b0)) !== 'b10) $stop;
    if ((f('b1) >> f('b1)) !== 'b0) $stop;
    if ((f('b100) >> f('b10)) !== 'b1) $stop;
    if ((f('b0x010000) >> f('b10)) !== 'b0x0100) $stop;
    if ((f('b0zx01) >> f('b10)) !== 'b0zx) $stop;
    if ((f('b1) >> f('b1x)) !== 'x) $stop;
    if ((f('b1) >> f('b1z)) !== 'x) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
