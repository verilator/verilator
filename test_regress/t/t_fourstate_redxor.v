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
    if (^f(0) !== 0) $stop;
    if (^f(1) !== 1) $stop;
    if (^f('x) !== 'x) $stop;
    if (^f('z) !== 'x) $stop;
    if (^f('b0000z0000) !== 'x) $stop;
    if (^f('b0000x0000) !== 'x) $stop;
    if (^f('b0000z0010) !== 'x) $stop;
    if (^f('b0000x0100) !== 'x) $stop;
    if (^f('b0000z0011) !== 'x) $stop;
    if (^f('b0000x0101) !== 'x) $stop;
    if (^f('b000000011) !== 0) $stop;
    if (^f('b000000101) !== 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
