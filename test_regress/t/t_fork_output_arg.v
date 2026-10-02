// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%p exp=%p\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Item;
  int value;
endclass

class Runner;
  task produce(output Item h, input int value);
    #1;
    h = new;
    h.value = value;
  endtask

  task replace(inout Item h);
    #1;
    `checkh(h.value, 1);
    h = new;
    h.value = 2;
  endtask

  task replace_ref(ref Item h);
    #1;
    h = new;
    h.value = 3;
  endtask

  task run;
    Item by_output, by_join, by_assign, by_inout, by_ref;
    static Item by_static;
    fork
      produce(by_output, 1);
      #10;
    join_any
    disable fork;
    `checkh(by_output != null, 1);
    `checkh(by_output.value, 1);

    fork
      produce(by_join, 4);
    join
    fork
      begin
        #1;
        by_assign = new;
        by_assign.value = 5;
      end
      #10;
    join_any
    disable fork;
    `checkh(by_join.value, 4);
    `checkh(by_assign.value, 5);

    by_inout = by_output;
    fork
      replace(by_inout);
      #10;
    join_any
    disable fork;
    `checkh(by_inout.value, 2);
    `checkh(by_output.value, 1);

    fork
      replace_ref(by_ref);
      #10;
    join_any
    disable fork;
    `checkh(by_ref != null, 1);
    `checkh(by_ref.value, 3);

    fork
      produce(by_static, 6);
      #10;
    join_any
    disable fork;
    `checkh(by_static.value, 6);
  endtask
endclass

class Cls;
  int x = 100;
  task get_x(output int arg);
    arg = x;
  endtask
endclass

task automatic test;
  int o;
  Cls c = new;
  fork
    c.get_x(o);
  join_any
  if (o != 100) $stop;
endtask

module t;
  Runner runner;
  initial begin
    runner = new;
    test();
    runner.run();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
