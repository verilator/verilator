// DESCRIPTION: Verilator: Wildcard imports become visible on first use
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package a_pkg;
  parameter int VALUE = 11;

  function automatic int get_value();
    return 11;
  endfunction

  task automatic set_value(output int result);
    result = 11;
  endtask

  class Item;
    function int value();
      return 11;
    endfunction
  endclass
endpackage

package b_pkg;
  parameter int VALUE = 22;

  function automatic int get_value();
    return 22;
  endfunction

  task automatic set_value(output int result);
    result = 22;
  endtask

  class Item;
    function int value();
      return 22;
    endfunction
  endclass
endpackage

module t;
  import a_pkg::*;

  // These references make a_pkg's four identifiers locally visible
  // before b_pkg is imported.
  localparam int first_value = VALUE;
  int first_function = get_value();
  int first_task;
  initial set_value(first_task);
  Item first_item;

  import b_pkg::*;

  // The second wildcard import cannot replace identifiers already
  // made locally visible by the preceding references.
  localparam int second_value = VALUE;
  int second_function = get_value();
  int second_task;
  initial set_value(second_task);
  Item second_item;

  initial begin
    // Both task calls run at time zero; check their results afterward.
    #0;
    first_item = new;
    second_item = new;

    `checkh(first_value, 11);
    `checkh(second_value, 11);
    `checkh(first_function, 11);
    `checkh(second_function, 11);
    `checkh(first_task, 11);
    `checkh(second_task, 11);
    `checkh(first_item.value(), 11);
    `checkh(second_item.value(), 11);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
