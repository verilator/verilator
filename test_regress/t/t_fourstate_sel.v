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
  function logic f(logic a);
    if (a === 1'b1) $write("1");
    else if (a === 1'b0) $write("0");
    else if (a === 1'bx) $write("x");
    else if (a === 1'bz) $write("z");
    else $stop;
    $write("\n");
    return a;
  endfunction

  function logic [5:0] bar();
    $write("Side effect\n");
    return 'b1x01xz;
  endfunction

  initial begin
    static logic [4:0] x = 5'bx1xz0;
    static bit [4:0] xx = 5'b11000;
    static logic y = 1;
    static logic z = 0;
    static logic [3:0] w = 7;
    static logic [3:0] a = 3;
    static bit [3:0] b = 3;
    static bit [3:0] c = 7;
    $write("0: ");
    f(x[`IMPURE_ONE ? 0 : 'x]);
    $write("1: ");
    f(x[`IMPURE_ONE ? 1 : 'x]);
    $write("2: ");
    f(x[`IMPURE_ONE ? 2 : 'x]);
    $write("3: ");
    f(x[`IMPURE_ONE ? 3 : 'x]);
    $write("4: ");
    f(x[`IMPURE_ONE ? 4 : 'x]);
    $write("y: ");
    f(x[`IMPURE_ONE ? y : 'x]);
    $write("z: ");
    f(x[`IMPURE_ONE ? z : 'x]);
    $write("w: ");
    f(x[`IMPURE_ONE ? w : 'x]);
    $write("a: ");
    f(x[`IMPURE_ONE ? a : 'x]);
    $write("b: ");
    f(x[`IMPURE_ONE ? b : 'x]);
    $write("c: ");
    f(x[`IMPURE_ONE ? c : 'x]);
    $write("0: ");
    f(xx[`IMPURE_ONE ? 0 : 'x]);
    $write("1: ");
    f(xx[`IMPURE_ONE ? 1 : 'x]);
    $write("2: ");
    f(xx[`IMPURE_ONE ? 2 : 'x]);
    $write("3: ");
    f(xx[`IMPURE_ONE ? 3 : 'x]);
    $write("4: ");
    f(xx[`IMPURE_ONE ? 4 : 'x]);
    $write("y: ");
    f(xx[`IMPURE_ONE ? y : 'x]);
    $write("z: ");
    f(xx[`IMPURE_ONE ? z : 'x]);
    $write("w: ");
    f(xx[`IMPURE_ONE ? w : 'x]);
    $write("a: ");
    f(xx[`IMPURE_ONE ? a : 'x]);
    $write("b: ");
    f(xx[`IMPURE_ONE ? b : 'x]);
    $write("c: ");
    f(xx[`IMPURE_ONE ? c : 'x]);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
