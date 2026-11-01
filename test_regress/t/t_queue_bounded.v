// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Base;
endclass

class Derived extends Base;
endclass

module t;

  localparam TWO = 2;

  int q[$ : TWO];  // Shall not go higher than [2], i.e. size 3

  initial begin
    q.push_front(3);
    if (q.size() != 1) $stop;
    q.push_front(2);
    if (q.size() != 2) $stop;
    q.push_front(1);
    if (q.size() != 3) $stop;
    q.push_front(0);
    if (q.size() != 3) $stop;
    q[3] = -1;
    if (q.size() != 3) $stop;
    if (q[0] != 0) $stop;
    if (q[1] != 1) $stop;
    if (q[2] != 2) $stop;

    q.delete();
    q.push_back(0);
    q.push_back(1);
    q.push_back(2);
    if (q.size() != 3) $stop;
    q.push_back(3);
    if (q.size() != 3) $stop;
    if (q[0] != 0) $stop;
    if (q[1] != 1) $stop;
    if (q[2] != 2) $stop;

    // Test insert on bounded queue
    q.delete();
    q.push_back(10);
    q.push_back(30);
    if (q.size() != 2) $stop;
    q.insert(1, 20);  // insert into middle while capacity remains
    if (q.size() != 3) $stop;
    if (q[0] != 10) $stop;
    if (q[1] != 20) $stop;
    if (q[2] != 30) $stop;
    // Insert on a full bounded queue discards the highest-numbered element (IEEE 1800-2023 7.10.3)
    q.insert(1, 99);
    `checkd(q.size(), 3);
    `checkd(q[0], 10);
    `checkd(q[1], 99);
    `checkd(q[2], 20);

    // Assigning a longer queue discards only the elements beyond the bound
    begin
      int src[$];
      int big[$:3];
      int same[$:TWO];
      src = '{1, 2, 3, 4, 5};
      q = src;
      `checkd(q.size(), 3);
      `checkd(q[0], 1);
      `checkd(q[1], 2);
      `checkd(q[2], 3);
      big = '{6, 7, 8, 9};
      q = big;
      `checkd(q.size(), 3);
      `checkd(q[0], 6);
      `checkd(q[1], 7);
      `checkd(q[2], 8);
      same = '{4, 5, 6};
      q = same;  // Same bound, nothing to discard
      `checkd(q.size(), 3);
      `checkd(q[2], 6);
      // Assignment pattern and unpacked array concatenation (IEEE 1800-2023 10.10)
      q = '{1, 2, 3, 4, 5, 6, 7};
      `checkd(q.size(), 3);
      `checkd(q[2], 3);
      q = {src, 9};
      `checkd(q.size(), 3);
      `checkd(q[2], 3);
    end

    begin
      string s[$:1];
      string src[$];
      src = '{"a", "b", "c"};
      s = src;
      `checkd(s.size(), 2);
      `checks(s[1], "b");
      // A concatenation of several items warns once, with the full attempted size
      s = {"d", "e", "f", "g"};
      `checkd(s.size(), 2);
      `checks(s[1], "e");
    end

    begin
      Base bq[$:1];
      Derived dq[$];
      Derived d;
      d = new;
      dq = '{d, d, d};
      bq = dq;
      `checkd(bq.size(), 2);
      bq.delete();
      bq = dq[0:2];  // From a temporary
      `checkd(bq.size(), 2);
    end

    begin
      typedef int bq1_t[$:1];
      typedef int bq2_t[$:2];
      typedef int bq3_t[$:3];
      bq3_t tq;
      tq = '{1, 2, 3, 4, 5, 6};
      `checkd(tq.size(), 4);
      `checkd(tq[3], 4);
      tq = {5, 6, 7, 8, 9, 10, 11};
      `checkd(tq.size(), 4);
      `checkd(tq[3], 8);
      // A spliced queue with a smaller bound is truncated first
      q = {bq1_t'{1, 2, 3}, 9};
      `checkd(q.size(), 3);
      `checkd(q[1], 2);
      `checkd(q[2], 9);
      // A spliced queue of another type with an equal bound
      q = {bq2_t'{4, 5, 6}, 7};
      `checkd(q.size(), 3);
      `checkd(q[2], 6);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
