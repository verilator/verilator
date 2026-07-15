// DESCRIPTION: Verilator: $finish propagation through expression-valued calls
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  int callback_after;
  int callback_before;
  int caller_after;
  int constructor_after;
  int constructor_before;
  int constructor_value_calls;
  int ctor_inout = 50;
  int ctor_out = 40;
  int left_gate;
  int method_calls;
  string mode;
  int passthrough_calls;
  int reduction_result = 77;
  int result = 99;
  int right_gate;
  int values[$] = '{3, 1, 2};

  class FinishCtor;
    int value;

    function new(bit fire);
      constructor_before++;
      if (fire) $finish;
      constructor_after++;
      value = 7;
    endfunction
  endclass

  class FinishCtorArgs;
    function new(output int out_value, inout int inout_value, input bit fire);
      constructor_before++;
      out_value = 11;
      inout_value++;
      if (fire) $finish;
      constructor_after++;
      out_value = 12;
      inout_value++;
    endfunction
  endclass

  class ValueCtor;
    int value;

    function new(int initial_value);
      constructor_value_calls++;
      value = initial_value;
    endfunction
  endclass

  class Box;
    int value;

    function new(int initial_value);
      value = initial_value;
    endfunction

    function int read_value();
      method_calls++;
      return value;
    endfunction
  endclass

  Box factory_handle;
  ValueCtor nested_handle;
  FinishCtorArgs user_args_handle;
  FinishCtor user_handle;

  function automatic int finish_value(int value);
    callback_before++;
    $finish;
    callback_after++;
    return value;
  endfunction

  function automatic int maybe_finish_value(int value, bit fire);
    callback_before++;
    if (fire) $finish;
    callback_after++;
    return value;
  endfunction

  function automatic int finish_value_on_call(int value, int call_number);
    callback_before++;
    if (callback_before == call_number) $finish;
    callback_after++;
    return value;
  endfunction

  function automatic Box finish_factory();
    callback_before++;
    $finish;
    callback_after++;
    return factory_handle;
  endfunction

  function automatic int passthrough(int value);
    passthrough_calls++;
    return value;
  endfunction

  task automatic run_reduction;
    reduction_result = values.sum with (finish_value(item));
    caller_after++;
  endtask

  task automatic run_reduction_complete;
    reduction_result = values.sum with (maybe_finish_value(item, 1'b0));
    caller_after++;
  endtask

  task automatic run_reduction_nested;
    reduction_result = values.sum with (passthrough(finish_value(item)));
    caller_after++;
  endtask

  task automatic run_reduction_sibling;
    reduction_result = values.sum with ((finish_value(item) != 0) ? item : passthrough(item));
    caller_after++;
  endtask

  task automatic run_sort;
    values.sort with (finish_value(item));
    caller_after++;
  endtask

  task automatic run_sort_complete;
    values.sort with (maybe_finish_value(item, 1'b0));
    caller_after++;
  endtask

  task automatic run_sort_late;
    values.sort with (finish_value_on_call(item, 3));
    caller_after++;
  endtask

  initial begin
    if (!$value$plusargs("MODE=%s", mode)) mode = "return";
    if (!$value$plusargs("LEFT_GATE=%d", left_gate)) left_gate = 0;
    if (!$value$plusargs("RIGHT_GATE=%d", right_gate)) right_gate = 1;
    factory_handle = new(55);

    if (mode == "return") begin
      result = 1 + finish_value(4);
      caller_after++;
    end
    else if (mode == "constructor") begin
      user_handle = new(1'b1);
      caller_after++;
    end
    else if (mode == "constructor_args") begin
      user_args_handle = new(ctor_out, ctor_inout, 1'b1);
      caller_after++;
    end
    else if (mode == "constructor_args_complete") begin
      user_args_handle = new(ctor_out, ctor_inout, 1'b0);
      caller_after++;
    end
    else if (mode == "constructor_arg_expr") begin
      nested_handle = new(finish_value(9));
      caller_after++;
    end
    else if (mode == "exprstmt") begin
      result = passthrough(finish_value(4));
      caller_after++;
    end
    else if (mode == "method_chain") begin
      result = finish_factory().read_value();
      caller_after++;
    end
    else if (mode == "short_circuit") begin
      if (((left_gate != 0) && (finish_value(
              1
          ) != 0)) || ((right_gate != 0) || (finish_value(
              2
          ) != 0)))
        caller_after++;
    end
    else if (mode == "reduction") begin
      run_reduction();
    end
    else if (mode == "reduction_complete") begin
      run_reduction_complete();
    end
    else if (mode == "reduction_nested") begin
      run_reduction_nested();
    end
    else if (mode == "reduction_sibling") begin
      run_reduction_sibling();
    end
    else if (mode == "sort") begin
      run_sort();
    end
    else if (mode == "sort_complete") begin
      run_sort_complete();
    end
    else if (mode == "sort_late") begin
      run_sort_late();
    end
    else begin
      $write("%%Error: Unknown mode '%s'\n", mode);
      `stop;
    end
  end

  final begin
    if (mode == "constructor") begin
      `checkd(constructor_before, 1);
      `checkd(constructor_after, 0);
      `checkd(user_handle == null, 1);
      `checkd(caller_after, 0);
    end
    else if (mode == "constructor_args") begin
      `checkd(constructor_before, 1);
      `checkd(constructor_after, 0);
      `checkd(user_args_handle == null, 1);
      `checkd(ctor_out, 40);
      `checkd(ctor_inout, 50);
      `checkd(caller_after, 0);
    end
    else if (mode == "constructor_args_complete") begin
      `checkd(constructor_before, 1);
      `checkd(constructor_after, 1);
      `checkd(user_args_handle != null, 1);
      `checkd(ctor_out, 12);
      `checkd(ctor_inout, 52);
      `checkd(caller_after, 1);
    end
    else if (mode == "constructor_arg_expr") begin
      `checkd(callback_before, 1);
      `checkd(callback_after, 0);
      `checkd(constructor_value_calls, 0);
      `checkd(nested_handle == null, 1);
      `checkd(caller_after, 0);
    end
    else if (mode == "short_circuit") begin
      `checkd(callback_before, 0);
      `checkd(callback_after, 0);
      `checkd(caller_after, 1);
    end
    else if (mode == "reduction_complete") begin
      `checkd(callback_before, 3);
      `checkd(callback_after, 3);
      `checkd(reduction_result, 6);
      `checkd(caller_after, 1);
    end
    else if (mode == "sort_complete") begin
      `checkd(callback_before != 0, 1);
      `checkd(callback_after, callback_before);
      `checkd(values.size(), 3);
      `checkd(values[0], 1);
      `checkd(values[1], 2);
      `checkd(values[2], 3);
      `checkd(caller_after, 1);
    end
    else if (mode == "sort_late") begin
      `checkd(callback_before, 3);
      `checkd(callback_after, 2);
      `checkd(values.size(), 3);
      `checkd(values[0], 3);
      `checkd(values[1], 1);
      `checkd(values[2], 2);
      `checkd(caller_after, 0);
    end
    else begin
      `checkd(callback_before, 1);
      `checkd(callback_after, 0);
      if (mode == "return") begin
        `checkd(result, 99);
      end
      else if (mode == "exprstmt") begin
        `checkd(result, 99);
        `checkd(passthrough_calls, 0);
      end
      else if (mode == "method_chain") begin
        `checkd(result, 99);
        `checkd(method_calls, 0);
      end
      else if (mode == "reduction" || mode == "reduction_nested" ||
               mode == "reduction_sibling") begin
        if (mode != "reduction") `checkd(passthrough_calls, 0);
        `checkd(reduction_result, 77);
      end
      else if (mode == "sort") begin
        `checkd(values.size(), 3);
        `checkd(values[0], 3);
        `checkd(values[1], 1);
        `checkd(values[2], 2);
      end
      `checkd(caller_after, 0);
    end
    $write("*-* All Finished *-*\n");
  end
endmodule
