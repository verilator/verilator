// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

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
    // Attempt insert on full bounded queue (should have no effect per IEEE 1800-2023)
    q.insert(1, 99);
    if (q.size() != 3) $stop;
    if (q[0] != 10) $stop;
    if (q[1] != 20) $stop;
    if (q[2] != 30) $stop;

    // Assigning a longer queue discards only the elements beyond the bound
    begin
      int src[$];
      int big[$:3];
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
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
