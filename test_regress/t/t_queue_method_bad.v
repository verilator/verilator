// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef int int_t;

  initial begin
    int q[$];
    int qe[$];  // Empty
    int qv[$];  // Value returns
    int qi[$];  // Index returns
    int i;
    int_t it;
    int aa[string];

    q = '{2, 2, 4, 1, 3};
    q.reverse(1);  // Bad no args allowed
    q.shuffle(1);  // Bad no args allowed
    qv = q.find;  // Bad missing with
    qv = q.find_first;  // Bad missing with
    qv = q.find_last;  // Bad missing with
    qi = q.find_index;  // Bad missing with
    qi = q.find_first_index;  // Bad missing with
    qi = q.find_last_index;  // Bad missing with

    qi = q.size with (1);  // with not allowed

    i = q.find_index(x) with (x == 2);  // Bad queue to int
    i = q.find(x) with (x == 2);  // Bad queue to int
    it = q.find_first_index(x) with (x == 2);  // Bad queue to typedef int
    i = aa.find_index(x) with (x == 2);  // Bad queue to int

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
