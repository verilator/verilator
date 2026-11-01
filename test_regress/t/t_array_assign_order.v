// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unpacked arrays assigned to reversed arrays at run time, by the left-to-right
// order of their elements (IEEE 1800-2023 7.6)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef int be_t[0:3];
typedef int le_t[3:0];

module sub (
    input le_t le,
    output le_t le_o
);
  assign le_o = '{30, 31, 32, 33};
  function automatic int left();
    return le[3];
  endfunction
endmodule

module t;
  // Values not known when verilating
  be_t be = '{
      $urandom_range(10, 10),
      $urandom_range(11, 11),
      $urandom_range(12, 12),
      $urandom_range(13, 13)
  };
  bit sel = $urandom_range(1, 1) == 1;

  // Assignment
  initial begin
    le_t le;
    le = be;
    `checkd(le[3], 10);
    `checkd(le[0], 13);
  end

  // Conditional of reversed operands
  initial begin
    le_t zero;
    le_t le_cond;
    zero = '{default: 0};
    le_cond = sel ? be : zero;
    `checkd(le_cond[3], 10);
    le_cond = !sel ? zero : be;
    `checkd(le_cond[0], 13);
  end

  // Function argument, and an element of it selected by a variable index
  function automatic int f_arg(le_t a);
    return a[3];
  endfunction
  function automatic int f_sel(le_t a, int k);
    return a[k];
  endfunction
  initial begin
    `checkd(f_arg(be), 10);
    `checkd(f_sel(be, $urandom_range(3, 3)), 10);
    `checkd(f_sel(be, $urandom_range(1, 1)), 12);
  end

  // Output and inout task arguments
  task automatic t_out(output le_t o);
    o = '{20, 21, 22, 23};
  endtask
  task automatic t_inout(inout le_t a);
    a[3] += 100;
  endtask
  initial begin
    be_t be_o;
    be_t be_io;
    t_out(be_o);
    `checkd(be_o[0], 20);
    `checkd(be_o[3], 23);
    be_io = be;
    t_inout(be_io);
    `checkd(be_io[0], 110);
    `checkd(be_io[3], 13);
  end

  // Pattern elements and members
  initial begin
    be_t be_b;
    int pe[2][3:0];
    struct {
      int a[3:0];
      int b;
    } sv;
    for (int i = 0; i < 4; ++i) be_b[i] = 50 + $urandom_range(i, i);
    pe = '{be, be};
    `checkd(pe[1][3], 10);
    `checkd(pe[1][0], 13);
    sv = '{a: be, b: 1};
    `checkd(sv.a[3], 10);
    `checkd(sv.a[0], 13);
    pe = '{1: be, 0: be_b};
    `checkd(pe[1][3], 10);
    `checkd(pe[0][3], 50);
    `checkd(pe[0][0], 53);
  end

  // Declaration with an initial value
  initial begin
    automatic le_t le_decl = be;
    `checkd(le_decl[3], 10);
  end

  // Nonblocking assignment, checked after it took effect
  initial begin
    le_t le_nba;
    le_nba <= be;
    #1;
    `checkd(le_nba[3], 10);
    `checkd(le_nba[0], 13);
  end

  // A slice
  initial begin
    int le_s[1:0];
    le_s = be[0:1];
    `checkd(le_s[1], 10);
    `checkd(le_s[0], 11);
    `checkd(le_s == be[0:1], 1'b1);
  end

  // Elements of an associative array, a dynamic array and a queue
  initial begin
    le_t aa[int];
    le_t da[];
    le_t q[$];
    aa[1] = be;
    `checkd(aa[1][3], 10);
    da = new[1];
    da[0] = be;
    `checkd(da[0][3], 10);
    q.push_back(be);
    `checkd(q[0][3], 10);
    q = {q, be};
    `checkd(q[1][3], 10);
    da = {da, be};
    `checkd(da[1][3], 10);
  end

  // Return value
  function automatic le_t f_ret();
    return be;
  endfunction
  initial begin
    le_t le_r;
    le_r = f_ret();
    `checkd(le_r[3], 10);
    `checkd(le_r[0], 13);
  end

  // Arrays of arrays, reversed in both, or only one level
  initial begin
    int be2[0:1][0:2];
    int le2[1:0][2:0];
    int outer[1:0][0:2];
    int inner[0:1][2:0];
    for (int i = 0; i < 2; ++i)
    for (int j = 0; j < 3; ++j) be2[i][j] = 10 * i + j + $urandom_range(0, 0);
    le2 = be2;
    `checkd(le2[1][2], 0);
    `checkd(le2[0][0], 12);
    `checkd(le2 == be2, 1'b1);
    outer = be2;
    `checkd(outer[1][0], 0);
    `checkd(outer[0][2], 12);
    inner = be2;
    `checkd(inner[0][2], 0);
    `checkd(inner[1][0], 12);
  end

  // Reversed in some dimensions only, the innermost included
  initial begin
    int be5[0:1][0:2][0:1][0:1][0:2];
    int mix5[0:1][2:0][0:1][0:1][2:0];
    for (int a = 0; a < 2; ++a)
    for (int b = 0; b < 3; ++b)
    for (int c = 0; c < 2; ++c)
    for (int d = 0; d < 2; ++d)
    for (int e = 0; e < 3; ++e)
    be5[a][b][c][d][e] = $urandom_range(10000 * a + 1000 * b + 100 * c + 10 * d + e,
                                        10000 * a + 1000 * b + 100 * c + 10 * d + e);
    mix5 = be5;
    for (int a = 0; a < 2; ++a)
    for (int b = 0; b < 3; ++b)
    for (int c = 0; c < 2; ++c)
    for (int d = 0; d < 2; ++d)
    for (int e = 0; e < 3; ++e) `checkd(mix5[a][2-b][c][d][2-e], be5[a][b][c][d][e]);
  end

  // Continuous assignment, and input and output port, checked after they took effect
  le_t le_w;
  be_t be_out;
  assign le_w = be;
  sub u_sub (
      .le(be),
      .le_o(be_out)
  );
  initial begin
    #1;
    `checkd(le_w[3], 10);
    `checkd(le_w[0], 13);
    `checkd(be == le_w, 1'b1);
    `checkd(u_sub.left(), 10);
    `checkd(be_out[0], 30);
    `checkd(be_out[3], 33);
  end

  // Equality, by the left-to-right order of elements (IEEE 1800-2023 7.4.6)
  initial begin
    le_t le;
    le = be;
    `checkd(le == be, 1'b1);
    `checkd(le === be, 1'b1);
    `checkd(le != be, 1'b0);
    // The same values at the same offsets, but in reverse left-to-right order
    le = '{13, 12, 11, 10};
    `checkd(le == be, 1'b0);
  end

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
