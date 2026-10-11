// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  // Typedefs
  typedef int myint_t;
  typedef int myint2_t;
  typedef int myq_t[$];
  typedef int myval_t;
  typedef string mykey_t;

  initial begin
    // Scalar
    automatic int a = 1, b = 1;

    // Unpacked array
    automatic int u1[2] = '{1, 2};
    automatic int u2[2] = '{1, 2};

    automatic int m1[2][2] = '{{1, 2}, {3, 4}};
    automatic int m2[2][2] = '{{1, 2}, {3, 4}};

    // Dynamic array
    automatic int d1[] = new[2];
    automatic int d2[] = new[2];

    // Queue
    automatic int q1[$] = '{10, 20};
    automatic int q2[$] = '{10, 20};

    // Associative array
    automatic int aa1[string];
    automatic int aa2[string];

    // Typedef array
    automatic myint_t t1[2] = '{1, 2};
    automatic myint2_t t2[2] = '{1, 2};

    // Typedef queue
    automatic myq_t tq1 = '{1, 2};
    automatic int tq2[$] = '{1, 2};

    // Typedef associative array
    automatic myval_t aa_typedef1[mykey_t];
    automatic int aa_typedef2[string];

    // Aggregate types
    automatic struct {int val;} s1 = '{0}, s2 = '{0};
    automatic
    union {
      int val;
      int other;
    }
        un1, un2;
    automatic
    enum {
      ENUM_A,
      ENUM_B,
      ENUM_C
    }
        e1 = ENUM_A, e2 = ENUM_A;

    // Packed structs with different definitions are equivalent by packed width
    automatic struct packed {bit [3:0] val;} ps1 = 0;
    automatic struct packed {bit [3:0] other;} ps2 = 0;

    // Typedef scalar
    automatic bit signed [31:0] b1 = 1;
    automatic int i1 = 1;

    d1[0] = 5;
    d1[1] = 6;
    d2[0] = 5;
    d2[1] = 6;

    aa1["a"] = 1;
    aa2["a"] = 1;
    aa1["b"] = 2;
    aa2["b"] = 2;

    aa_typedef1["foo"] = 123;
    aa_typedef2["foo"] = 123;

    un1.val = 1;
    un2.val = 1;

    if (a != b) $fatal(0, "Scalar comparison failed");
    if (u1 != u2) $fatal(0, "Unpacked 1D array comparison failed");
    if (m1 != m2) $fatal(0, "Unpacked multi-dimensional array comparison failed");
    if (d1 != d2) $fatal(0, "Dynamic array comparison failed");
    if (q1 != q2) $fatal(0, "Queue comparison failed");
    if (aa1 != aa2) $fatal(0, "Associative array comparison failed");
    if (t1 != t2) $fatal(0, "Typedef unpacked array comparison failed");
    if (tq1 != tq2) $fatal(0, "Typedef queue comparison failed");
    if (aa_typedef1 != aa_typedef2) $fatal(0, "Typedef associative array comparison failed");
    if (b1 != i1) $fatal(0, "bit[31:0] vs int comparison failed");

    if (s1 != s2) $fatal(0, "Unpacked struct comparison failed");
    if (un1 != un2) $fatal(0, "Unpacked union comparison failed");
    if (e1 != e2) $fatal(0, "Enum comparison failed");
    if (ps1 != ps2) $fatal(0, "Packed struct comparison failed");

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
