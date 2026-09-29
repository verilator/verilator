// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Foo;
  int queue[$];
  Foo fooQ[$];
  int q;
  function void modify_q();
    q = 10;
  endfunction
endclass

module t;
  int queue2[$];
  Foo fooQ2[$];
  int q[$];
  bit [3:0] nib;
  bit [63:0] q64[$];
  bit [63:0] w;

  initial begin
    static Foo foo = new;

    `checkd(foo.queue.size(), 0);
    `checkd(queue2.size(), 0);

    foo.queue.push_back(7);
    `checkd(foo.queue.size(), 1);
    `checkd(foo.queue[0], 7);
    `checkd(queue2.size(), 0);

    queue2.push_back(foo.queue.pop_front());
    `checkd(foo.queue.size(), 0);
    `checkd(queue2.size(), 1);
    `checkd(queue2[0], 7);

    foo.queue.push_back(queue2.pop_back());
    `checkd(foo.queue.size(), 1);
    `checkd(foo.queue[0], 7);
    `checkd(queue2.size(), 0);

    `checkd(foo.fooQ.size(), 0);
    `checkd(fooQ2.size(), 0);

    foo.fooQ.push_back(foo);
    `checkd(foo.fooQ.size(), 1);
    if (foo.fooQ[0] != foo) $stop;
    `checkd(fooQ2.size(), 0);

    `checkd(foo.fooQ[0].queue.size(), 1);
    `checkd(foo.fooQ[0].queue[0], 7);

    `checkd(foo.fooQ[0].queue.pop_front(), 7);
    `checkd(foo.fooQ[0].queue.size(), 0);

    fooQ2.push_back(foo.fooQ.pop_back());
    `checkd(foo.fooQ.size(), 0);
    `checkd(fooQ2.size(), 1);
    if (fooQ2[0] != foo) $stop;

    foo.fooQ.push_back(fooQ2.pop_back());
    `checkd(foo.fooQ.size(), 1);
    if (foo.fooQ[0] != foo) $stop;
    `checkd(fooQ2.size(), 0);

    `checkd(foo.fooQ[0].q, 0);
    foo.fooQ[0].modify_q();
    `checkd(foo.fooQ[0].q, 10);
    foo.fooQ[0].q = 14;
    `checkd(foo.fooQ[0].q, 14);

    foo.fooQ[0].queue.push_back(7);
    `checkd(foo.fooQ[0].queue.size(), 1);
    `checkd(foo.fooQ[0].queue[0], 7);
    `checkd(queue2.size(), 0);

    queue2.push_back(foo.fooQ[0].queue.pop_front());
    `checkd(foo.fooQ[0].queue.size(), 0);
    `checkd(queue2.size(), 1);
    `checkd(queue2[0], 7);

    foo.fooQ[0].queue.push_back(queue2.pop_back());
    `checkd(foo.fooQ[0].queue.size(), 1);
    `checkd(foo.fooQ[0].queue[0], 7);
    `checkd(queue2.size(), 0);

    foo.fooQ[0] = new;
    if (foo.fooQ[0] == foo) $stop;

    q.push_back(32'hA5);
    nib = q.pop_front()[3:0] ^ 4'hF;
    `checkd(nib, 4'hA);
    `checkd(q.size(), 0);

    q.push_back(32'hA5);
    `checkd((q.pop_front()[3:0] === 4'h5), 1'b1);
    `checkd(q.size(), 0);

    q.push_back(5);
    q.push_back(5);
    q64.push_back({q.pop_front(), q.pop_front()});
    `checkd(q64.size(), 1);
    `checkd(q64[0], 64'h5_0000_0005);
    `checkd(q.size(), 0);

    q.push_back(32'hD);
    q64.push_back({q.pop_front(), 32'h1});
    `checkd(q64.size(), 2);
    `checkd(q64[1], 64'hD_0000_0001);
    `checkd(q.size(), 0);

    q.push_back(9);
    q.push_back(9);
    w = {q.pop_front(), q.pop_front()};
    `checkd(w, 64'h9_0000_0009);
    `checkd(q.size(), 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
