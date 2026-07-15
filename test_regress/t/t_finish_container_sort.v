// DESCRIPTION: Verilator: $finish propagation through container sort callbacks
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  localparam int RECEIVER_QUEUE = 1;
  localparam int RECEIVER_DYNAMIC = 2;
  localparam int RECEIVER_FIXED = 3;

  class ContainerBox;
    int values[$];

    function new();
      values = '{3, 1, 2};
    endfunction
  endclass

  int callback_after;
  int callback_before;
  int caller_after;
  int dynamic_values[];
  int expected_trigger;
  int fixed_values[3];
  bit is_descending;
  string mode;
  int receiver_kind;
  ContainerBox box;

  function automatic int sort_key(int value);
    callback_before++;
    if ((expected_trigger != 0) && (callback_before == expected_trigger)) $finish;
    callback_after++;
    return value;
  endfunction

  task automatic run_queue(input bit descending, input int trigger);
    expected_trigger = trigger;
    is_descending = descending;
    receiver_kind = RECEIVER_QUEUE;
    if (descending) box.values.rsort with (sort_key(item));
    else box.values.sort with (sort_key(item));
    caller_after++;
  endtask

  task automatic run_dynamic(input bit descending, input int trigger);
    expected_trigger = trigger;
    is_descending = descending;
    receiver_kind = RECEIVER_DYNAMIC;
    if (descending) dynamic_values.rsort with (sort_key(item));
    else dynamic_values.sort with (sort_key(item));
    caller_after++;
  endtask

  task automatic run_fixed(input bit descending, input int trigger);
    expected_trigger = trigger;
    is_descending = descending;
    receiver_kind = RECEIVER_FIXED;
    if (descending) fixed_values.rsort with (sort_key(item));
    else fixed_values.sort with (sort_key(item));
    caller_after++;
  endtask

  task automatic check_queue(input bit original);
    `checkd(box.values.size(), 3);
    if (original) begin
      `checkd(box.values[0], 3);
      `checkd(box.values[1], 1);
      `checkd(box.values[2], 2);
    end
    else if (is_descending) begin
      `checkd(box.values[0], 3);
      `checkd(box.values[1], 2);
      `checkd(box.values[2], 1);
    end
    else begin
      `checkd(box.values[0], 1);
      `checkd(box.values[1], 2);
      `checkd(box.values[2], 3);
    end
  endtask

  task automatic check_dynamic(input bit original);
    `checkd(dynamic_values.size(), 3);
    if (original) begin
      `checkd(dynamic_values[0], 3);
      `checkd(dynamic_values[1], 1);
      `checkd(dynamic_values[2], 2);
    end
    else if (is_descending) begin
      `checkd(dynamic_values[0], 3);
      `checkd(dynamic_values[1], 2);
      `checkd(dynamic_values[2], 1);
    end
    else begin
      `checkd(dynamic_values[0], 1);
      `checkd(dynamic_values[1], 2);
      `checkd(dynamic_values[2], 3);
    end
  endtask

  task automatic check_fixed(input bit original);
    `checkd($size(fixed_values), 3);
    if (original) begin
      `checkd(fixed_values[0], 3);
      `checkd(fixed_values[1], 1);
      `checkd(fixed_values[2], 2);
    end
    else if (is_descending) begin
      `checkd(fixed_values[0], 3);
      `checkd(fixed_values[1], 2);
      `checkd(fixed_values[2], 1);
    end
    else begin
      `checkd(fixed_values[0], 1);
      `checkd(fixed_values[1], 2);
      `checkd(fixed_values[2], 3);
    end
  endtask

  initial begin
    box = new;
    dynamic_values = new[3];
    dynamic_values = '{3, 1, 2};
    fixed_values = '{3, 1, 2};

    if (!$value$plusargs("MODE=%s", mode)) begin
      $write("%%Error: Missing MODE plusarg\n");
      `stop;
    end

    if (mode == "queue_sort_first") run_queue(1'b0, 1);
    else if (mode == "queue_sort_late") run_queue(1'b0, 3);
    else if (mode == "queue_sort_complete") run_queue(1'b0, 0);
    else if (mode == "queue_rsort_first") run_queue(1'b1, 1);
    else if (mode == "queue_rsort_late") run_queue(1'b1, 3);
    else if (mode == "queue_rsort_complete") run_queue(1'b1, 0);
    else if (mode == "dynamic_sort_first") run_dynamic(1'b0, 1);
    else if (mode == "dynamic_sort_late") run_dynamic(1'b0, 3);
    else if (mode == "dynamic_sort_complete") run_dynamic(1'b0, 0);
    else if (mode == "dynamic_rsort_first") run_dynamic(1'b1, 1);
    else if (mode == "dynamic_rsort_late") run_dynamic(1'b1, 3);
    else if (mode == "dynamic_rsort_complete") run_dynamic(1'b1, 0);
    else if (mode == "fixed_sort_first") run_fixed(1'b0, 1);
    else if (mode == "fixed_sort_late") run_fixed(1'b0, 3);
    else if (mode == "fixed_sort_complete") run_fixed(1'b0, 0);
    else if (mode == "fixed_rsort_first") run_fixed(1'b1, 1);
    else if (mode == "fixed_rsort_late") run_fixed(1'b1, 3);
    else if (mode == "fixed_rsort_complete") run_fixed(1'b1, 0);
    else begin
      $write("%%Error: Unknown mode '%s'\n", mode);
      `stop;
    end
  end

  final begin
    if (expected_trigger == 0) begin
      `checkd(callback_before != 0, 1);
      `checkd(callback_after, callback_before);
      `checkd(caller_after, 1);
    end
    else begin
      `checkd(callback_before, expected_trigger);
      `checkd(callback_after, expected_trigger - 1);
      `checkd(caller_after, 0);
    end

    if (receiver_kind == RECEIVER_QUEUE) check_queue(expected_trigger != 0);
    else if (receiver_kind == RECEIVER_DYNAMIC) check_dynamic(expected_trigger != 0);
    else if (receiver_kind == RECEIVER_FIXED) check_fixed(expected_trigger != 0);
    else begin
      $write("%%Error: Invalid receiver kind %0d\n", receiver_kind);
      `stop;
    end
    $write("*-* All Finished *-*\n");
  end
endmodule
