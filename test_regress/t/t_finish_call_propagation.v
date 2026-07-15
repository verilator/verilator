// DESCRIPTION: Verilator: $finish propagation through source calls
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// verilog_format: off
interface class FinishDispatch;
  pure virtual task run(input bit fire, ref int leaf_after, ref int normal_count);
endclass

interface class DiamondFinishRoot;
  pure virtual task run_diamond(input bit fire, ref int leaf_after, ref int normal_count);
endclass

interface class DiamondFinishLeft extends DiamondFinishRoot;
endclass

interface class DiamondFinishRight extends DiamondFinishRoot;
endclass

interface class DiamondFinishLeaf extends DiamondFinishLeft, DiamondFinishRight;
endclass
// verilog_format: on

class FinishImplementation implements FinishDispatch;
  virtual task run(input bit fire, ref int leaf_after, ref int normal_count);
    if (fire) begin
      $finish;
      leaf_after++;
    end
    else begin
      normal_count++;
    end
  endtask
endclass

class NormalImplementation implements FinishDispatch;
  virtual task run(input bit fire, ref int leaf_after, ref int normal_count);
    normal_count++;
  endtask
endclass

class DiamondFinishImplementation implements DiamondFinishLeaf;
  virtual task run_diamond(input bit fire, ref int leaf_after, ref int normal_count);
    if (fire) begin
      $finish;
      leaf_after++;
    end
    else begin
      normal_count++;
    end
  endtask
endclass

class ExternFinishBase;
  extern virtual function int query_extern(input bit fire, input int value);
  extern virtual task run_extern(input bit fire, ref int leaf_after, ref int normal_count);
endclass

function int ExternFinishBase::query_extern(input bit fire, input int value);
  if (fire) $finish;
  return value;
endfunction

task ExternFinishBase::run_extern(input bit fire, ref int leaf_after, ref int normal_count);
  normal_count++;
endtask

class ExternFinishDerived extends ExternFinishBase;
  virtual task run_extern(input bit fire, ref int leaf_after, ref int normal_count);
    if (fire) begin
      $finish;
      leaf_after++;
    end
    else begin
      normal_count++;
    end
  endtask
endclass

virtual class PureFinishBase;
  pure virtual function int query(input bit fire, input string name);
endclass

class PureFinishDerived extends PureFinishBase;
  virtual function int query(input bit fire, input string name);
    if (fire) $finish;
    return name.len();
  endfunction
endclass

class ParamFinish #(
    type T = int
);
  static function T create(input bit fire, input T value);
    if (fire) $finish;
    return value;
  endfunction
endclass

typedef ParamFinish#(PureFinishBase) ObjectParamFinish;

module t;
  int direct_after;
  int direct_normal_leaf;
  int diamond_leaf_after;
  int diamond_normal_count;
  int diamond_wrapper_after;
  int dpi_export_after;
  int dpi_output_value = 50;
  int dpi_pure_after;
  int dpi_pure_result;
  int dpi_task_after;
  int extern_leaf_after;
  int extern_normal_count;
  int extern_query_result;
  int false_path_count;
  int initial_after;
  int inout_value = 20;
  int interface_leaf_after;
  int interface_normal_count;
  int interface_wrapper_after;
  int leaf_after;
  int mutual_a_after;
  int mutual_b_after;
  int mutual_normal_leaf;
  int out_value = 10;
  PureFinishBase param_result;
  int pure_virtual_result;
  int ref_value = 30;
  int recursive_function_after;
  int recursive_function_caller_after;
  int recursive_function_finish_result = 77;
  int recursive_function_normal_result;
  int task_after;
  int wrapper_after;
  string test_case;

  import "DPI-C" context dpi_reenter_finish = function int dpi_reenter_finish_alias();
  import "DPI-C" pure function int dpi_pure_value(input int value);

  export "DPI-C" function sv_finish_export;
  function automatic int sv_finish_export();
    $finish;
    dpi_export_after++;
    return 99;
  endfunction

  class Base;
    virtual task leaf(bit fire, ref int ref_arg);
      if (fire) begin
        $finish;
        leaf_after++;
      end
      else begin
        false_path_count++;
      end
    endtask

    task wrapper(bit fire, ref int ref_arg);
      leaf(fire, ref_arg);
      wrapper_after++;
    endtask
  endclass

  class Derived extends Base;
    virtual task leaf(bit fire, ref int ref_arg);
      if (fire) begin
        $finish;
        leaf_after++;
      end
      else begin
        false_path_count++;
      end
    endtask
  endclass

  Base object;
  DiamondFinishRoot diamond_object;
  ExternFinishBase extern_object;
  FinishDispatch interface_object;
  PureFinishBase pure_object;

  task automatic direct_recursive(input int depth, input bit fire);
    if (depth == 0) begin
      if (fire) begin
        $finish;
        direct_after++;
      end
      else begin
        direct_normal_leaf++;
      end
    end
    else begin
      direct_recursive(depth - 1, fire);
      direct_after++;
    end
  endtask

  task automatic mutual_a(input int depth, input bit fire);
    if (depth == 0) begin
      if (fire) begin
        $finish;
        mutual_a_after++;
      end
      else begin
        mutual_normal_leaf++;
      end
    end
    else begin
      mutual_b(depth - 1, fire);
      mutual_a_after++;
    end
  endtask

  task automatic mutual_b(input int depth, input bit fire);
    if (depth == 0) begin
      if (fire) begin
        $finish;
        mutual_b_after++;
      end
      else begin
        mutual_normal_leaf++;
      end
    end
    else begin
      mutual_a(depth - 1, fire);
      mutual_b_after++;
    end
  endtask

  function automatic int recursive_function(input int depth, input bit fire);
    int child_result;
    if (depth == 0) begin
      if (fire) begin
        $finish;
        recursive_function_after++;
      end
      return 1;
    end
    child_result = recursive_function(depth - 1, fire);
    recursive_function_after++;
    return child_result + 1;
  endfunction

  task automatic invoke(output int out_arg, inout int inout_arg, ref int ref_arg);
    out_arg = 11;
    inout_arg = 21;
    ref_arg = 31;
    object.wrapper(1'b1, ref_arg);
    task_after++;
    out_arg = 12;
    inout_arg = 22;
    ref_arg = 32;
  endtask

  task automatic invoke_interface(input bit fire);
    interface_object.run(fire, interface_leaf_after, interface_normal_count);
    interface_wrapper_after++;
  endtask

  task automatic invoke_diamond(input bit fire);
    diamond_object.run_diamond(fire, diamond_leaf_after, diamond_normal_count);
    diamond_wrapper_after++;
  endtask

  task automatic invoke_dpi(output int out_arg);
    out_arg = 51;
    out_arg = dpi_reenter_finish_alias();
    dpi_task_after++;
    out_arg = 52;
  endtask

  initial begin
    DiamondFinishImplementation diamond_implementation;
    Derived derived;
    ExternFinishDerived extern_derived;
    FinishImplementation finish_implementation;
    NormalImplementation normal_implementation;
    PureFinishDerived pure_derived;
    if (!$value$plusargs("CASE=%s", test_case)) $fatal(1, "Missing +CASE");
    derived = new;
    diamond_implementation = new;
    extern_derived = new;
    finish_implementation = new;
    normal_implementation = new;
    pure_derived = new;
    object = derived;
    object.leaf(1'b0, ref_value);
    direct_recursive(2, 1'b0);
    mutual_a(3, 1'b0);
    recursive_function_normal_result = recursive_function(2, 1'b0);
    dpi_pure_result = dpi_pure_value(40);
    dpi_pure_after++;
    diamond_object = diamond_implementation;
    invoke_diamond(1'b0);
    extern_object = extern_derived;
    extern_object.run_extern(1'b0, extern_leaf_after, extern_normal_count);
    extern_query_result = extern_object.query_extern(1'b0, 13);
    interface_object = normal_implementation;
    invoke_interface(1'b0);
    pure_object = pure_derived;
    pure_virtual_result = pure_object.query(1'b0, "normal");
    param_result = ObjectParamFinish::create(1'b0, pure_object);
    if (test_case == "direct") direct_recursive(2, 1'b1);
    else if (test_case == "mutual") mutual_a(3, 1'b1);
    else if (test_case == "interface") begin
      interface_object = finish_implementation;
      invoke_interface(1'b1);
    end
    else if (test_case == "interface_diamond") invoke_diamond(1'b1);
    else if (test_case == "extern_virtual") begin
      extern_object.run_extern(1'b1, extern_leaf_after, extern_normal_count);
    end
    else if (test_case == "extern_function") begin
      extern_query_result = 77;
      extern_query_result = extern_object.query_extern(1'b1, 13);
    end
    else if (test_case == "pure_virtual") begin
      pure_virtual_result = 77;
      pure_virtual_result = pure_object.query(1'b1, "finish");
    end
    else if (test_case == "param_function") begin
      param_result = null;
      param_result = ObjectParamFinish::create(1'b1, pure_object);
    end
    else if (test_case == "dpi") invoke_dpi(dpi_output_value);
    else if (test_case == "recursive_function") begin
      recursive_function_finish_result = recursive_function(2, 1'b1);
      recursive_function_caller_after++;
    end
    else if (test_case == "virtual") invoke(out_value, inout_value, ref_value);
    else $fatal(1, "Unknown +CASE=%s", test_case);
    initial_after++;
  end

  final begin
    object.leaf(1'b0, ref_value);
    `checkd(direct_after, 2);
    `checkd(direct_normal_leaf, 1);
    `checkd(diamond_leaf_after, 0);
    `checkd(diamond_normal_count, 1);
    `checkd(diamond_wrapper_after, 1);
    `checkd(dpi_export_after, 0);
    `checkd(dpi_output_value, 50);
    `checkd(dpi_pure_after, 1);
    `checkd(dpi_pure_result, 41);
    `checkd(dpi_task_after, 0);
    `checkd(extern_leaf_after, 0);
    `checkd(extern_normal_count, 1);
    `checkd(extern_query_result, (test_case == "extern_function") ? 77 : 13);
    `checkd(false_path_count, 2);
    `checkd(interface_leaf_after, 0);
    `checkd(interface_normal_count, 1);
    `checkd(interface_wrapper_after, 1);
    `checkd(leaf_after, 0);
    `checkd(mutual_a_after, 2);
    `checkd(mutual_b_after, 1);
    `checkd(mutual_normal_leaf, 1);
    `checkd(wrapper_after, 0);
    `checkd(task_after, 0);
    `checkd(initial_after, 0);
    `checkd(out_value, 10);
    `checkd(param_result == null, test_case == "param_function");
    `checkd(pure_virtual_result, (test_case == "pure_virtual") ? 77 : 6);
    `checkd(inout_value, 20);
    `checkd(ref_value, (test_case == "virtual") ? 31 : 30);
    `checkd(recursive_function_after, 2);
    `checkd(recursive_function_caller_after, 0);
    `checkd(recursive_function_finish_result, 77);
    `checkd(recursive_function_normal_result, 3);
    $write("*-* All Finished *-*\n");
  end
endmodule

`ifdef TEST_PUBLIC
module public_top;
  int final_after  /* verilator public */;
  bit implicit_property_finish  /* verilator public */;
  int implicit_property_commit_after  /* verilator public */;
  int implicit_property_initializer_after  /* verilator public */;
  int initial_after  /* verilator public */;
  int nested_after  /* verilator public */;
  int property_commit_after  /* verilator public */;
  int property_constructor_after  /* verilator public */;
  bit property_finish  /* verilator public */;
  int property_initializer_after  /* verilator public */;
  int public_after  /* verilator public */;
  int static_public_after  /* verilator public */;

  class PropertyFinish;
    int value = initialize_value();

    function automatic int initialize_value();
      if (property_finish) $finish;
      property_initializer_after++;
      return 9;
    endfunction

    function new();
      property_constructor_after++;
    endfunction
  endclass

  class ImplicitPropertyFinish;
    int value = initialize_value();

    function automatic int initialize_value();
      if (implicit_property_finish) $finish;
      implicit_property_initializer_after++;
      return 10;
    endfunction
  endclass

  ImplicitPropertyFinish implicit_property_object;
  PropertyFinish property_object;

  task automatic nested_finish();
    $finish;
    nested_after++;
  endtask

  function automatic int public_finish();
    // verilator public
    $finish;
    public_after++;
    return 99;
  endfunction

  function int public_static_finish(input bit fire);
    // verilator public
    if (fire) $finish;
    static_public_after++;
    return 123;
  endfunction

  task automatic public_property_initializer_finish();
    // verilator public
    property_object = new;
    property_commit_after++;
  endtask

  task automatic public_implicit_property_initializer_finish();
    // verilator public
    implicit_property_object = new;
    implicit_property_commit_after++;
  endtask

  function automatic bit public_implicit_property_object_is_null();
    // verilator public
    return implicit_property_object == null;
  endfunction

  function automatic bit public_property_object_is_null();
    // verilator public
    return property_object == null;
  endfunction

  initial begin
    nested_finish();
    initial_after++;
  end
  final begin
    $finish;
    final_after++;
  end
endmodule
`endif
