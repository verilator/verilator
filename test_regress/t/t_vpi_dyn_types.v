// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns / 1ns

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  class C;
    int x;
  endclass

  typedef struct {
    int a;
    int q[$];
  } s_t;

  int q[$];
  int da[];
  int aa[int];
  C c;
  C carr[2];
  mailbox #(int) mb;
  semaphore sem;
  event ev;
  s_t st;
  string str;
  logic [7:0] lg;
  bit woke;

  initial begin
    q.push_back(1);
    da = new[2];
    da[1] = 7;
    aa[1] = 2;
    c = new;
    c.x = 5;
    carr[0] = new;
    carr[0].x = 6;
    mb = new;
    mb.put(8);
    sem = new(1);
    st.a = 3;
    st.q.push_back(4);
    str = "str";
    lg = 8'h5a;
    fork
      begin
        @ev;
        woke = 1;
      end
    join_none
    #10;
    ->ev;
    #1;
    `checkd(woke, 1'b1);
    `checkd(q.size(), 1);
    `checkd(q[0], 1);
    `checkd(da.size(), 2);
    `checkd(da[1], 7);
    `checkd(aa.size(), 1);
    `checkd(aa[1], 2);
    `checkd(c != null, 1'b1);
    `checkd(c.x, 5);
    `checkd(carr[0] != null, 1'b1);
    `checkd(carr[0].x, 6);
    `checkd(carr[1] == null, 1'b1);
    `checkd(mb.num(), 1);
    `checkd(sem.try_get(1), 1);
    `checkd(st.a, 3);
    `checkd(st.q.size(), 1);
    `checkd(st.q[0], 4);
    `checkd(str == "str", 1'b1);
    `checkd(lg, 8'h5a);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
