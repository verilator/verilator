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

  task automatic get_item_after_delay(output Item item);
    #1;
    item = new;
    item.value0 = 89;
  endtask

  task automatic set_int(output int value);
    value = 90;
  endtask

  task automatic run;
    static Item item;
    item = null;

    fork : isolation_fork0
      fork
        #5;
        get_item(item);
      join_any
      disable fork;
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
        get_item_assign(item);
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

  task automatic run_automatic;
    Item item;
    item = null;

    fork : isolation_fork3
      begin
        fork
          get_item_after_delay(item);
        join_any
      end
    join

    `checkd(item != null, 1);
    `checkd(item.value0, 89);
  endtask

  task automatic run_array_element;
    Item items[1];
    items[0] = null;

    fork : isolation_fork4
      begin
        fork
          get_item_after_delay(items[0]);
        join_any
      end
    join

    `checkd(items[0] != null, 1);
    `checkd(items[0].value0, 89);
  endtask

  function automatic int get_value(Item item);
    return item.value0;
  endfunction

  // Handle is only read inside the fork (RHS and call argument),
  // while the parent later reassigns it
  task automatic run_read_only;
    Item item = new;
    Item orig;
    int rhs_before, arg_before;
    int rhs_after, arg_after;
    item.value0 = 1;
    orig = item;

    fork
      begin
        // Runs at time 0, before the parent reassigns the handle
        rhs_before = item.value0;
        arg_before = get_value(item);
        #2;
        // Runs after the parent reassigned the shared handle
        rhs_after = item.value0;
        arg_after = get_value(item);
      end
    join_none

    #1;
    item = new;
    item.value0 = 2;
    #2;

    `checkd(rhs_before, 1);
    `checkd(arg_before, 1);
    `checkd(rhs_after, 2);
    `checkd(arg_after, 2);
    `checkd(orig.value0, 1);  // original object untouched
  endtask

  task automatic run_non_class;
    int value;

    fork
      set_int(value);
    join

    `checkd(value, 90);
  endtask
endclass

module t;
  initial begin
    Driver driver;

    driver = new;
    driver.run();
    driver.run_automatic();
    driver.run_array_element();
    driver.run_read_only();
    driver.run_non_class();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
