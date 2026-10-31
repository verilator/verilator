// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

typedef struct {
  int x;
  int y;
} pair_t;

class Cls;
  int q[$];
  int d[];
  int m[int];
  pair_t s;
endclass

module t (
    input clk
);

  integer i;
  reg [94:0] w95;
  reg [399:0] w400;

  integer cyc = 0;

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d\n", $time, cyc);
`endif
    cyc <= cyc + 1;
    if (cyc == 0) begin
      // Setup
      w95 = {95{1'b1}};
      w400 = '1;
    end
    else if (cyc == 1) begin
      if (w95++ != {95{1'b1}}) $stop;
      if (w95 != {95{1'b0}}) $stop;
      if (w95-- != {95{1'b0}}) $stop;
      if (w95 != {95{1'b1}}) $stop;
      if (++w95 != {95{1'b0}}) $stop;
      if (w95 != {95{1'b0}}) $stop;
      if (--w95 != {95{1'b1}}) $stop;
      if (w95 != {95{1'b1}}) $stop;

      if (w400++ != {400{1'b1}}) $stop;
      if (w400 != {400{1'b0}}) $stop;
      if (w400-- != {400{1'b0}}) $stop;
      if (w400 != {400{1'b1}}) $stop;
      if (++w400 != {400{1'b0}}) $stop;
      if (w400 != {400{1'b0}}) $stop;
      if (--w400 != {400{1'b1}}) $stop;
      if (w400 != {400{1'b1}}) $stop;
    end
    else if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Patterns assigned to a non-variable lvalue they also read
  initial begin
    Cls c1;
    Cls c2;
    int aq[2][$];
    c1 = new;
    c2 = new;

    c1.q = {1, 2};
    c2.q = {3};
    c1.q = {c1.q, c2.q};
    if ($sformatf("%p", c1.q) != "'{'h1, 'h2, 'h3}") $stop;

    c1.d = {4, 5};
    c1.d = {c1.d, c1.d};
    if ($sformatf("%p", c1.d) != "'{'h4, 'h5, 'h4, 'h5}") $stop;

    c1.m[2] = 6;
    c1.m[3] = 7;
    c1.m = '{1: c1.m[2], 2: c1.m[3]};
    if ($sformatf("%p", c1.m) != "'{'h1:'h6, 'h2:'h7}") $stop;

    c1.s = '{8, 9};
    c1.s = '{c1.s.y, c1.s.x};
    if ($sformatf("%p", c1.s) != "'{x:'h9, y:'h8}") $stop;

    aq[0] = {10};
    aq[1] = {11};
    aq[1] = {aq[1], aq[0]};
    if ($sformatf("%p", aq) != "'{'{'ha}, '{'hb, 'ha}}") $stop;
  end

  // Array method 'with' results assigned to an lvalue they also read
  initial begin
    Cls c;
    int aq[int][$];
    int qq[$][$];
    int fq[1:3][$];
    int dq[][$];
    aq[1] = {3, 2, 3};
    aq[5] = {1, 3};
    foreach (aq[k]) aq[k] = aq[k].find with (item != 3);
    `checkp(aq, "'{'h1:'{'h2}, 'h5:'{'h1}}");
    qq = '{'{3, 4, 3}, '{5}};
    foreach (qq[k]) qq[k] = qq[k].find with (item != 3);
    `checkp(qq, "'{'{'h4}, '{'h5}}");
    fq = '{'{3, 7}, '{8, 3, 3}, '{}};
    foreach (fq[k]) fq[k] = fq[k].find with (item != 3);
    `checkp(fq, "'{'{'h7}, '{'h8}, '{}}");
    dq = new[2];
    dq[0] = {3, 9};
    dq[1] = {3};
    foreach (dq[k]) dq[k] = dq[k].find with (item != 3);
    `checkp(dq, "'{'{'h9}, '{}}");
    c = new;
    c.q = {1, 5, 2, 6};
    c.q = c.q.find with (item > 2);
    `checkp(c.q, "'{'h5, 'h6}");
  end

  // Other array methods with 'with', using the index or a named iterator
  initial begin
    int aq[int][$];
    aq[0] = {4, 3, 5, 3};
    foreach (aq[k]) aq[k] = aq[k].find_index with (item == 3);
    `checkp(aq, "'{'h0:'{'h1, 'h3}}");
    aq[0] = {4, 3, 5, 3};
    foreach (aq[k]) aq[k] = aq[k].find_first(x) with (x > 3);
    `checkp(aq, "'{'h0:'{'h4}}");
    aq[0] = {4, 3, 5, 3};
    foreach (aq[k]) aq[k] = aq[k].find_last with (item.index < 3);
    `checkp(aq, "'{'h0:'{'h5}}");
    aq[0] = {4, -3, 5};
    foreach (aq[k]) aq[k] = aq[k].min with (item * item);
    `checkp(aq, "'{'h0:'{'hfffffffd}}");
    aq[0] = {4, -7, 5};
    foreach (aq[k]) aq[k] = aq[k].max(x) with (x * x);
    `checkp(aq, "'{'h0:'{'hfffffff9}}");
    aq[0] = {5, 5};
    foreach (aq[k]) aq[k] = aq[k].unique with (item % 10);
    `checkp(aq, "'{'h0:'{'h5}}");
  end

  // Nested 'with', and string and wide elements
  initial begin
    int aq[int][$];
    int p[$];
    string sq[int][$];
    bit [64:0] wq[int][$];
    p = {2, 4};
    aq[0] = {1, 2, 3, 4};
    foreach (aq[k]) aq[k] = aq[k].find(x) with (p.sum(y) with (int'(y == x)) == 0);
    `checkp(aq, "'{'h0:'{'h1, 'h3}}");
    sq[0] = {"a", "bb", "c"};
    foreach (sq[k]) sq[k] = sq[k].find with (item.len() == 1);
    `checkp(sq, "'{'h0:'{\"a\", \"c\"}}");
    wq[0].push_back(65'h1);
    wq[0].push_back({65{1'b1}});
    wq[0].push_back(65'h3);
    foreach (wq[k]) wq[k] = wq[k].find with (item[64]);
    `checkp(wq, "'{'h0:'{'h1ffffffffffffffff}}");
  end
endmodule
