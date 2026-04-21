// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  int x;
  int int_q[$];
  int dyn[];

  function new();
    x = 0;
    int_q = '{12, 13, 17, 19};
    dyn = '{21, 22, 23};
  endfunction

  task rand_with_queue();
    int ok;
    ok = std::randomize(x) with {x inside {int_q};};
    `checkd(ok, 1);
    `checkd(int_q.size(), 4);
    `checkd(int_q[0], 12);
    `checkd(int_q[1], 13);
    `checkd(int_q[2], 17);
    `checkd(int_q[3], 19);
    if (!(x inside {int_q})) `stop;
  endtask

  task rand_with_dyn();
    int ok;
    ok = std::randomize(x) with {x inside {dyn};};
    `checkd(ok, 1);
    `checkd(dyn.size(), 3);
    `checkd(dyn[0], 21);
    `checkd(dyn[1], 22);
    `checkd(dyn[2], 23);
    if (!(x inside {dyn})) `stop;
  endtask
endclass

module t;
  Cls obj;

  initial begin
    obj = new();
    repeat (20) obj.rand_with_queue();
    repeat (20) obj.rand_with_dyn();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
