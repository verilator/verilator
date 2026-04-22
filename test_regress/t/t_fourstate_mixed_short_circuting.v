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

  function logic bar();
    calls++;
    return 'x;
  endfunction

  initial begin
    if ((bit'(`IMPURE_ONE) || bit'(bar() || ('x && 1))) !== 1) $stop;
    if ((bit'(!`IMPURE_ONE) && bit'(bar() || ('x && 1))) !== 0) $stop;
    if ((`IMPURE_ONE ? 0 : bit'(bar())) !== 0) $stop;
    if (calls !== 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
