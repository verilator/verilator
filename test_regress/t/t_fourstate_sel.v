// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

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
    f(x[0]);
    $write("1: ");
    f(x[1]);
    $write("2: ");
    f(x[2]);
    $write("3: ");
    f(x[3]);
    $write("4: ");
    f(x[4]);
    $write("y: ");
    f(x[y]);
    $write("z: ");
    f(x[z]);
    $write("w: ");
    f(x[w]);
    $write("a: ");
    f(x[a]);
    $write("b: ");
    f(x[b]);
    $write("c: ");
    f(x[c]);
    $write("0: ");
    f(xx[0]);
    $write("1: ");
    f(xx[1]);
    $write("2: ");
    f(xx[2]);
    $write("3: ");
    f(xx[3]);
    $write("4: ");
    f(xx[4]);
    $write("y: ");
    f(xx[y]);
    $write("z: ");
    f(xx[z]);
    $write("w: ");
    f(xx[w]);
    $write("a: ");
    f(xx[a]);
    $write("b: ");
    f(xx[b]);
    $write("c: ");
    f(xx[c]);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
