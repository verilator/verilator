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
  function logic f(logic x);
    if (`IMPURE_ONE) return x;
    return 'x;
  endfunction

  initial begin
    if ({f(1'b0), f(1'b0)} !== 2'b00) $stop;
    if ({f(1'b0), f(1'b1)} !== 2'b01) $stop;
    if ({f(1'b0), f(1'bx)} !== 2'b0x) $stop;
    if ({f(1'b0), f(1'bz)} !== 2'b0z) $stop;

    if ({f(1'b1), f(1'b0)} !== 2'b10) $stop;
    if ({f(1'b1), f(1'b1)} !== 2'b11) $stop;
    if ({f(1'b1), f(1'bx)} !== 2'b1x) $stop;
    if ({f(1'b1), f(1'bz)} !== 2'b1z) $stop;

    if ({f(1'bz), f(1'b0)} !== 2'bz0) $stop;
    if ({f(1'bz), f(1'b1)} !== 2'bz1) $stop;
    if ({f(1'bz), f(1'bx)} !== 2'bzx) $stop;
    if ({f(1'bz), f(1'bz)} !== 2'bzz) $stop;

    if ({f(1'bx), f(1'b0)} !== 2'bx0) $stop;
    if ({f(1'bx), f(1'b1)} !== 2'bx1) $stop;
    if ({f(1'bx), f(1'bx)} !== 2'bxx) $stop;
    if ({f(1'bx), f(1'bz)} !== 2'bxz) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
