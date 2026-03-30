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
  static int calls = 0;

  function logic f(logic a);
    if (a === 1'b1) $write("1");
    else if (a === 1'b0) $write("0");
    else if (a === 1'bx) $write("x");
    else if (a === 1'bz) $write("z");
    else $stop;
    $write("\n");
    return a;
  endfunction


  function logic bar();
    calls++;
    return 'x;
  endfunction

  initial begin
    if ((f(0) ? f(1) : f(0)) !== 0) $stop;
    if ((f(1) ? f(1) : f(0)) !== 1) $stop;
    if ((f('x) ? f(1) : f(0)) !== 'x) $stop;
    if ((f('x) ? f(1) : f(1)) !== 1) $stop;
    if ((f('z) ? f(1) : f(0)) !== 'x) $stop;
    if ((f('z) ? f(0) : f(0)) !== 0) $stop;
    if ((`IMPURE_ONE ? 0 : bar()) !== 0) $stop;
    if (calls !== 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
