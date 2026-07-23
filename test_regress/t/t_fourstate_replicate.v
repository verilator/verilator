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
    if ({1{f(1'b0)}} !== 1'b0) $stop;
    if ({1{f(1'b1)}} !== 1'b1) $stop;
    if ({1{f(1'bx)}} !== 1'bx) $stop;
    if ({1{f(1'bz)}} !== 1'bz) $stop;

    if ({2{f(1'b0)}} !== 2'b00) $stop;
    if ({2{f(1'b1)}} !== 2'b11) $stop;
    if ({2{f(1'bx)}} !== 2'bxx) $stop;
    if ({2{f(1'bz)}} !== 2'bzz) $stop;

    if ({3{f(1'b0)}} !== 3'b000) $stop;
    if ({3{f(1'b1)}} !== 3'b111) $stop;
    if ({3{f(1'bx)}} !== 3'bxxx) $stop;
    if ({3{f(1'bz)}} !== 3'bzzz) $stop;

    if ({4{f(1'b0)}} !== 4'b0000) $stop;
    if ({4{f(1'b1)}} !== 4'b1111) $stop;
    if ({4{f(1'bx)}} !== 4'bxxxx) $stop;
    if ({4{f(1'bz)}} !== 4'bzzzz) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
