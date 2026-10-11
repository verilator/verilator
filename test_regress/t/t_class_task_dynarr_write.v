// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class other;
  task y(output int arg);
    arg = 2;
  endtask
endclass

class cls;
  task dynarrayout(inout int arr[]);
    automatic other o = new;
    o.y(arr[0]);
  endtask
  task dynarrayref(ref int arr[]);
    automatic other o = new;
    o.y(arr[0]);
  endtask
  task queueref(ref int q[$]);
    automatic other o = new;
    o.y(q[0]);
  endtask
  task queueout(inout int q[$]);
    automatic other o = new;
    o.y(q[0]);
  endtask
endclass

module t;
  cls c;
  int arr[];
  int q  [$];

  initial begin
    c = new;
    arr = new[1];

    arr[0] = 6;
    c.dynarrayref(arr);
    `checkd(arr[0], 2);
    `checkd(arr.size(), 1);

    arr[0] = 9;
    c.dynarrayout(arr);
    `checkd(arr[0], 2);
    `checkd(arr.size(), 1);

    q.push_back(981);
    c.queueref(q);
    `checkd(q[0], 2);
    `checkd(q.size(), 1);
    q.pop_front();

    q.push_back(981);
    c.queueout(q);
    `checkd(q[0], 2);
    `checkd(q.size(), 1);
    q.pop_front();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
