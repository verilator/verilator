// DESCRIPTION: Verilator: Test X/Z four-state simulation with comparisons
//
// This test verifies four-state simulation with comparison operators.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t;

  reg [3:0] a = 4'b1010;
  reg [3:0] b = 4'b0101;
  reg [3:0] x = 4'bX010;
  reg [3:0] z = 4'bZ010;
  reg [3:0] xall = 4'bXXXX;
  reg [3:0] zall = 4'bZZZZ;

  reg eq, ne, lt, le, gt, ge;
  reg eq_x, ne_x;
  reg case_eq, case_ne;
  reg case_eq_x;

  initial begin
    eq = (a == b);
    ne = (a != b);
    lt = (a < b);
    le = (a <= b);
    gt = (a > b);
    ge = (a >= b);

    eq_x = (a == x);
    ne_x = (a != x);

    case_eq = (a === b);
    case_ne = (a !== b);
    case_eq_x = (a === x);

    $write("=== Basic Comparisons (no X/Z) ===\n");
    $write("a == b = %b (expect 0)\n", eq);
    $write("a != b = %b (expect 1)\n", ne);
    $write("a < b = %b (expect 0)\n", lt);
    $write("a > b = %b (expect 1)\n", gt);

    $write("\n=== Comparisons with X ===\n");
    $write("a == x = %b\n", eq_x);
    $write("a != x = %b\n", ne_x);

    $write("\n=== Case Equality ===\n");
    $write("a === b = %b\n", case_eq);
    $write("a !== b = %b\n", case_ne);
    $write("a === x = %b\n", case_eq_x);
    $write("xall === xall = %b (X never matches X)\n", xall === xall);
    $write("zall === zall = %b (Z never matches Z)\n", zall === zall);

    $write("\n=== Reduction with X/Z ===\n");
    $write("& x = %b\n", &x);
    $write("| x = %b\n", |x);
    $write("^ x = %b\n", ^x);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
