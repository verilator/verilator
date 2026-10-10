// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Item;
  int value0;
  static int value1;
  static int value2;
  int value3;
endclass

class Driver;
  task automatic get_item(output Item item);
    item = new;
    item.value0 = 83;
    item.value1 = 84;
    item.value2 = 85;
    item.value3 = #1 86;
    item.value1 <= 87;
    item.value2 <= #1 88;
  endtask

  task automatic get_item_dly(output Item item);
    item.value2 <= #1 80;
  endtask

  task automatic get_item_assign(output Item item);
    item.value2 = 81;
  endtask

  task automatic run;
    static Item item;
    item = null;

    fork : isolation_fork0
      fork
        get_item(item);
      join_any
    join

    if (item == null) `stop;

    `checkd(item.value0, 83);
    `checkd(item.value1, 84);
    `checkd(item.value2, 85);
    `checkd(item.value3, 86);
    #1;
    `checkd(item.value1, 87);
    #1;
    `checkd(item.value2, 88);

    // Isolated test for ASSIGNDLY node only
    fork : isolation_fork1
      fork
        get_item_dly(item);
      join_any
    join

    #2;
    `checkd(item.value2, 80);

    // Isolated test for ASSIGN node only
    fork : isolation_fork2
      fork
        get_item_assign(item);
      join_any
    join

    `checkd(item.value2, 81);
  endtask
endclass

// This test makes sure that when passing class object as an argument
// to function call inside fork inside another fork, the object will
// be passed as a reference, so any changes made to this object will
// be visible outside the fork.

module t;
  initial begin
    Driver driver;

    driver = new;
    driver.run();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
