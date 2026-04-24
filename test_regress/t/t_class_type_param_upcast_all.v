// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Legal upcasts on class type-parameter args, direct and multi-level.

class Base;
  int seq = 0;
  int b_tag = 'hBAAD;
endclass

class Mid extends Base;
  int m_tag = 'hDEAD;
endclass

class Leaf extends Mid;
  int l_tag = 'hBEEF;
endclass

class Unrelated;
  int u_tag = 0;
endclass

class Fifo #(type T = Unrelated);
  T m_val;
  task put(input T t);
    m_val = t;
  endtask
  task get(output T t);
    t = m_val;
  endtask
endclass

module t;
  Fifo #(Leaf) lf;
  Fifo #(Mid)  mf;
  Fifo #(Base) bf;

  Leaf  l1, l2, l3;
  Mid   m1, m2;
  Base  b1, b2, b3;

  initial begin
    lf = new;
    mf = new;
    bf = new;

    // Output upcast Leaf -> Mid.
    l1 = new; l1.seq = 1;
    lf.put(l1);
    lf.get(m1);
    if (m1 === null) $stop;
    if (m1.seq !== 1) $stop;

    // Output upcast Leaf -> Base (two levels).
    l2 = new; l2.seq = 2;
    lf.put(l2);
    lf.get(b1);
    if (b1 === null) $stop;
    if (b1.seq !== 2) $stop;

    // Output upcast Mid -> Base.
    m2 = new; m2.seq = 3;
    mf.put(m2);
    mf.get(b2);
    if (b2 === null) $stop;
    if (b2.seq !== 3) $stop;

    // Input upcast Leaf -> Base.
    l3 = new; l3.seq = 4;
    bf.put(l3);
    bf.get(b3);
    if (b3 === null) $stop;
    if (b3.seq !== 4) $stop;

    // Same-type sanity.
    m1 = new; m1.seq = 5;
    mf.put(m1);
    mf.get(m2);
    if (m2 === null) $stop;
    if (m2.seq !== 5) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
