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
    if (&f('b00000000000000000000000000000000) !== 0) $stop;
    if (&f('b00000000000000000000000000000100) !== 0) $stop;
    if (&f('b10000000000000000000000000010100) !== 0) $stop;
    if (&f('b0000000000000000000000000000000x) !== 0) $stop;
    if (&f('b00000000000000000000000000000z0x) !== 0) $stop;
    if (&f('b00000000000000000000000000000z00) !== 0) $stop;
    if (&f('b0xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx) !== 0) $stop;
    if (&f('b1xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx) !== 'x) $stop;
    if (&f('b1zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz) !== 'x) $stop;
    if (&f('b1zzzzzzzzzzzzzzzzzzzzzxxxxxxxxxx) !== 'x) $stop;
    if (&f('b1111111111111111111111111111111x) !== 'x) $stop;
    if (&f('b1111111111111111111111111111111z) !== 'x) $stop;
    if (&f('b11111111111111111111111111111111) !== 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
