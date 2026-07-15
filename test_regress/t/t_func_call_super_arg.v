// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class base;
  static int constructor_calls;

  function new(string name);
    constructor_calls++;
    $display(name);
    if (name == "42") $finish;
  endfunction

  function string retstr();
    return $sformatf("%0d", $c("42"));
  endfunction
endclass

class derived extends base;
  static int after_super;

  function new(output int out_value, inout int inout_value);
    super.new(retstr());
    out_value = 11;
    inout_value++;
    after_super++;
  endfunction
endclass

class base_plain;
  static int constructor_calls;

  function new(string name);
    constructor_calls++;
    $display(name);
  endfunction
endclass

class derived_arg extends base_plain;
  static int after_name;
  static int after_super;

  function string finish_name();
    $finish;
    after_name++;
    return "unreachable";
  endfunction

  function new(output int out_value, inout int inout_value);
    super.new(finish_name());
    out_value = 11;
    inout_value++;
    after_super++;
  endfunction
endclass

class finish_helpers;
  static int after_name;

  static function string finish_name();
    $finish;
    after_name++;
    return "unreachable";
  endfunction
endclass

class base_outer;
  static int constructor_calls;

  function new();
    constructor_calls++;
  endfunction
endclass

class derived_outer extends base_outer;
  static int constructor_calls;

  function new(string name);
    super.new();
    constructor_calls++;
  endfunction
endclass

class derived_nested extends base_plain;
  static int after_name;
  static int after_super;
  static int passthrough_calls;

  function string finish_name();
    $finish;
    after_name++;
    return "unreachable";
  endfunction

  function string passthrough(string name);
    passthrough_calls++;
    return name;
  endfunction

  function new();
    super.new(passthrough(finish_name()));
    after_super++;
  endfunction
endclass

class base_int;
  static int constructor_calls;

  function new(int value);
    constructor_calls++;
  endfunction
endclass

class derived_conditional extends base_int;
  static int after_super;
  static int finish_calls;

  function int finish_argument();
    finish_calls++;
    $finish;
    return 1;
  endfunction

  function new(bit do_finish);
    super.new(do_finish ? finish_argument() : 7);
    after_super++;
  endfunction
endclass

class derived_callback extends base_int;
  static int after_callback;
  static int after_super;
  static int callback_calls;
  static int values[3] = '{3, 1, 2};

  function int finish_value(int value);
    callback_calls++;
    $finish;
    after_callback++;
    return value;
  endfunction

  function new();
    super.new(values.sum with (finish_value(item)));
    after_super++;
  endfunction
endclass

class base_multi;
  static int constructor_calls;

  function new(int first, int second);
    constructor_calls++;
  endfunction
endclass

class derived_multi extends base_multi;
  static int after_super;
  static int argument_calls;

  function int finish_argument(int value);
    argument_calls++;
    $finish;
    return value;
  endfunction

  function new();
    super.new(finish_argument(1), finish_argument(2));
    after_super++;
  endfunction
endclass

class derived_complete extends base_multi;
  static int after_super;
  static int argument_calls;

  function int maybe_finish_argument(int value, bit do_finish);
    argument_calls++;
    if (do_finish) $finish;
    return value;
  endfunction

  function new();
    super.new(maybe_finish_argument(1, 0), 2);
    after_super++;
  endfunction
endclass

class derived_mixed extends base_multi;
  static int after_finish_sibling;
  static int after_super;
  static int finish_calls;
  static bit finish_seen;
  static int sibling_calls;

  function int finish_argument();
    finish_calls++;
    finish_seen = 1;
    $finish;
    return 1;
  endfunction

  function int sibling_argument();
    sibling_calls++;
    if (finish_seen) after_finish_sibling++;
    return 2;
  endfunction

  function new();
    super.new(finish_argument(), sibling_argument());
    after_super++;
  endfunction
endclass

class derived_mixed_reverse extends base_multi;
  static int after_finish_sibling;
  static int after_super;
  static int finish_calls;
  static bit finish_seen;
  static int sibling_calls;

  function int finish_argument();
    finish_calls++;
    finish_seen = 1;
    $finish;
    return 2;
  endfunction

  function int sibling_argument();
    sibling_calls++;
    if (finish_seen) after_finish_sibling++;
    return 1;
  endfunction

  function new();
    super.new(sibling_argument(), finish_argument());
    after_super++;
  endfunction
endclass

class base_writable;
  static int constructor_calls;

  function new(int first, output int second);
    constructor_calls++;
    second = first;
  endfunction
endclass

class derived_writable extends base_writable;
  static int after_super;
  static int finish_calls;

  function int finish_argument(bit do_finish);
    finish_calls++;
    if (do_finish) $finish;
    return 1;
  endfunction

  function new(output int out_value, input bit do_finish);
    super.new(finish_argument(do_finish), out_value);
    after_super++;
  endfunction
endclass

class derived_writable_complete extends base_writable;
  static int after_super;

  function new(output int out_value);
    super.new(7, out_value);
    after_super++;
  endfunction
endclass

class base_inout_plain;
  static int constructor_calls;

  function new(inout int value);
    constructor_calls++;
    value += 3;
  endfunction
endclass

class derived_inout_plain extends base_inout_plain;
  static int after_super;

  function new(inout int value);
    super.new(value);
    after_super++;
  endfunction
endclass

class base_inout_finish;
  static int constructor_calls;

  function new(int first, inout int second);
    constructor_calls++;
    second += first;
  endfunction
endclass

class derived_inout_finish extends base_inout_finish;
  static int after_super;
  static int finish_calls;

  function int finish_argument(bit do_finish);
    finish_calls++;
    if (do_finish) $finish;
    return 3;
  endfunction

  function new(inout int value, input bit do_finish);
    super.new(finish_argument(do_finish), value);
    after_super++;
  endfunction
endclass

class base_ref;
  static int constructor_calls;

  function new(int first, ref int second);
    constructor_calls++;
    second = first;
  endfunction
endclass

class derived_ref extends base_ref;
  static int after_super;
  static int finish_calls;

  function int finish_argument();
    finish_calls++;
    $finish;
    return 1;
  endfunction

  function new(ref int ref_value);
    super.new(finish_argument(), ref_value);
    after_super++;
  endfunction
endclass

class derived_ref_complete extends base_ref;
  static int after_super;

  function new(ref int ref_value);
    super.new(9, ref_value);
    after_super++;
  endfunction
endclass

class base_ref_complex;
  static int constructor_calls;

  function new(input int first, ref int second, input int third);
    constructor_calls++;
    second = first + third;
  endfunction
endclass

class derived_ref_complex extends base_ref_complex;
  static int after_finish_index;
  static int after_super;
  static int finish_calls;
  static bit finish_seen;
  static int index_calls;
  static int values[2] = '{60, 61};

  function int finish_argument();
    finish_calls++;
    finish_seen = 1;
    $finish;
    return 1;
  endfunction

  function int index_argument();
    index_calls++;
    if (finish_seen) after_finish_index++;
    return 0;
  endfunction

  function new();
    super.new(finish_argument(), values[index_argument()], 0);
    after_super++;
  endfunction
endclass

class derived_ref_complex_reverse extends base_ref_complex;
  static int after_finish_index;
  static int after_super;
  static int finish_calls;
  static bit finish_seen;
  static int index_calls;
  static int values[2] = '{60, 61};

  function int finish_argument();
    finish_calls++;
    finish_seen = 1;
    $finish;
    return 1;
  endfunction

  function int index_argument();
    index_calls++;
    if (finish_seen) after_finish_index++;
    return 0;
  endfunction

  function new();
    super.new(0, values[index_argument()], finish_argument());
    after_super++;
  endfunction
endclass

class derived_ref_complex_complete extends base_ref_complex;
  static int after_super;
  static int index_calls;
  static int values[2] = '{60, 61};

  function int maybe_finish_argument(bit do_finish);
    if (do_finish) $finish;
    return 4;
  endfunction

  function int index_argument();
    index_calls++;
    return 1;
  endfunction

  function new();
    super.new(maybe_finish_argument(0), values[index_argument()], 5);
    after_super++;
  endfunction
endclass

class derived_ref_complex_index_finish extends base_ref_complex;
  static int after_index;
  static int after_super;
  static int index_calls;
  static int values[2] = '{60, 61};

  function int index_argument();
    index_calls++;
    $finish;
    after_index++;
    return 0;
  endfunction

  function new();
    super.new(1, values[index_argument()], 2);
    after_super++;
  endfunction
endclass

class derived_ref_queue_complete extends base_ref_complex;
  static int after_super;
  static int index_calls;
  static int values[$] = '{60, 61};

  function int maybe_finish_argument(bit do_finish);
    if (do_finish) $finish;
    return 4;
  endfunction

  function int index_argument();
    index_calls++;
    return 1;
  endfunction

  function new();
    super.new(maybe_finish_argument(0), values[index_argument()], 5);
    after_super++;
  endfunction
endclass

class base_const_ref;
  static int constructor_calls;

  function new(int first, const ref int second);
    constructor_calls++;
  endfunction
endclass

class derived_const_ref extends base_const_ref;
  static int after_super;
  static int finish_calls;

  function int finish_argument();
    finish_calls++;
    $finish;
    return 1;
  endfunction

  function new(const ref int ref_value);
    super.new(finish_argument(), ref_value);
    after_super++;
  endfunction
endclass

class base_const_ref_complex;
  static int constructor_calls;
  static int observed;

  function new(input int first, const ref int second, input int third);
    constructor_calls++;
    observed = first + second + third;
  endfunction
endclass

class derived_const_ref_complex extends base_const_ref_complex;
  static int after_finish_index;
  static int after_super;
  static int finish_calls;
  static bit finish_seen;
  static int values[2] = '{60, 61};

  function int finish_argument();
    finish_calls++;
    finish_seen = 1;
    $finish;
    return 1;
  endfunction

  function int index_argument();
    if (finish_seen) after_finish_index++;
    return 0;
  endfunction

  function new();
    super.new(finish_argument(), values[index_argument()], 0);
    after_super++;
  endfunction
endclass

class derived_const_ref_complex_reverse extends base_const_ref_complex;
  static int after_finish_index;
  static int after_super;
  static int finish_calls;
  static bit finish_seen;
  static int values[2] = '{60, 61};

  function int finish_argument();
    finish_calls++;
    finish_seen = 1;
    $finish;
    return 1;
  endfunction

  function int index_argument();
    if (finish_seen) after_finish_index++;
    return 0;
  endfunction

  function new();
    super.new(0, values[index_argument()], finish_argument());
    after_super++;
  endfunction
endclass

class derived_const_ref_complex_complete extends base_const_ref_complex;
  static int after_super;
  static int index_calls;
  static int values[2] = '{60, 61};

  function int maybe_finish_argument(bit do_finish);
    if (do_finish) $finish;
    return 4;
  endfunction

  function int index_argument();
    index_calls++;
    return 1;
  endfunction

  function new();
    super.new(maybe_finish_argument(0), values[index_argument()], 5);
    after_super++;
  endfunction
endclass

class derived_const_ref_complex_index_finish extends base_const_ref_complex;
  static int after_index;
  static int after_super;
  static int index_calls;
  static int values[2] = '{60, 61};

  function int index_argument();
    index_calls++;
    $finish;
    after_index++;
    return 0;
  endfunction

  function new();
    super.new(1, values[index_argument()], 2);
    after_super++;
  endfunction
endclass

class grandparent_chain;
  static int constructor_calls;

  function new(int value);
    constructor_calls++;
  endfunction
endclass

class parent_chain extends grandparent_chain;
  static int after_super;

  function new(int value);
    super.new(value);
    after_super++;
  endfunction
endclass

class derived_chain extends parent_chain;
  static int after_super;
  static int finish_calls;

  function int finish_argument();
    finish_calls++;
    $finish;
    return 1;
  endfunction

  function new();
    super.new(finish_argument());
    after_super++;
  endfunction
endclass

class default_arg_ctor;
  static int after_default;
  static int constructor_calls;
  static int default_calls;

  static function int finish_default();
    default_calls++;
    $finish;
    after_default++;
    return 1;
  endfunction

  function new(int value = finish_default());
    constructor_calls++;
  endfunction
endclass

class derived_default_arg extends default_arg_ctor;
  static int after_super;

  function new();
    super.new();
    after_super++;
  endfunction
endclass

module t;
  int inout_value = 50;
  string mode;
  int out_value = 40;
  int ref_value = 60;

  initial begin
    if (!$value$plusargs("MODE=%s", mode)) mode = "base";
    if (mode == "base") begin
      automatic derived test = new(out_value, inout_value);
    end
    else if (mode == "argument") begin
      automatic derived_arg test = new(out_value, inout_value);
    end
    else if (mode == "caller_argument") begin
      automatic derived_outer test = new(finish_helpers::finish_name());
    end
    else if (mode == "nested_argument") begin
      automatic derived_nested test = new();
    end
    else if (mode == "conditional_argument") begin
      automatic derived_conditional test = new(1);
    end
    else if (mode == "conditional_complete") begin
      automatic derived_conditional test = new(0);
      $finish;
    end
    else if (mode == "callback_argument") begin
      automatic derived_callback test = new();
    end
    else if (mode == "multiple_arguments") begin
      automatic derived_multi test = new();
    end
    else if (mode == "non_finishing_argument") begin
      automatic derived_complete test = new();
      $finish;
    end
    else if (mode == "mixed_arguments") begin
      automatic derived_mixed test = new();
    end
    else if (mode == "mixed_arguments_reverse") begin
      automatic derived_mixed_reverse test = new();
    end
    else if (mode == "writable_sibling") begin
      automatic derived_writable test = new(out_value, 1'b1);
    end
    else if (mode == "writable_guarded_complete") begin
      automatic derived_writable test = new(out_value, 1'b0);
      $finish;
    end
    else if (mode == "writable_complete") begin
      automatic derived_writable_complete test = new(out_value);
      $finish;
    end
    else if (mode == "inout_complete") begin
      automatic derived_inout_plain test = new(inout_value);
      $finish;
    end
    else if (mode == "inout_sibling") begin
      automatic derived_inout_finish test = new(inout_value, 1'b1);
    end
    else if (mode == "inout_guarded_complete") begin
      automatic derived_inout_finish test = new(inout_value, 1'b0);
      $finish;
    end
    else if (mode == "ref_sibling") begin
      automatic derived_ref test = new(ref_value);
    end
    else if (mode == "ref_complete") begin
      automatic derived_ref_complete test = new(ref_value);
      $finish;
    end
    else if (mode == "ref_complex") begin
      automatic derived_ref_complex test = new();
    end
    else if (mode == "ref_complex_reverse") begin
      automatic derived_ref_complex_reverse test = new();
    end
    else if (mode == "ref_complex_complete") begin
      automatic derived_ref_complex_complete test = new();
      $finish;
    end
    else if (mode == "ref_complex_index_finish") begin
      automatic derived_ref_complex_index_finish test = new();
    end
    else if (mode == "ref_queue_complete") begin
      automatic derived_ref_queue_complete test = new();
      $finish;
    end
    else if (mode == "const_ref_sibling") begin
      automatic derived_const_ref test = new(ref_value);
    end
    else if (mode == "const_ref_complex") begin
      automatic derived_const_ref_complex test = new();
    end
    else if (mode == "const_ref_complex_reverse") begin
      automatic derived_const_ref_complex_reverse test = new();
    end
    else if (mode == "const_ref_complex_complete") begin
      automatic derived_const_ref_complex_complete test = new();
      $finish;
    end
    else if (mode == "const_ref_complex_index_finish") begin
      automatic derived_const_ref_complex_index_finish test = new();
    end
    else if (mode == "constructor_chain") begin
      automatic derived_chain test = new();
    end
    else if (mode == "default_argument") begin
      automatic default_arg_ctor test = new();
    end
    else if (mode == "default_super_argument") begin
      automatic derived_default_arg test = new();
    end
    else begin
      $write("%%Error: Unknown mode '%s'\n", mode);
      `stop;
    end
  end

  final begin
    if (mode == "base") begin
      `checkd(base::constructor_calls, 1);
      `checkd(derived::after_super, 0);
    end
    else if (mode == "argument") begin
      `checkd(base_plain::constructor_calls, 0);
      `checkd(derived_arg::after_name, 0);
      `checkd(derived_arg::after_super, 0);
    end
    else if (mode == "caller_argument") begin
      `checkd(finish_helpers::after_name, 0);
      `checkd(base_outer::constructor_calls, 0);
      `checkd(derived_outer::constructor_calls, 0);
    end
    else if (mode == "nested_argument") begin
      `checkd(derived_nested::after_name, 0);
      `checkd(derived_nested::passthrough_calls, 0);
      `checkd(base_plain::constructor_calls, 0);
      `checkd(derived_nested::after_super, 0);
    end
    else if (mode == "conditional_argument") begin
      `checkd(derived_conditional::finish_calls, 1);
      `checkd(base_int::constructor_calls, 0);
      `checkd(derived_conditional::after_super, 0);
    end
    else if (mode == "conditional_complete") begin
      `checkd(derived_conditional::finish_calls, 0);
      `checkd(base_int::constructor_calls, 1);
      `checkd(derived_conditional::after_super, 1);
    end
    else if (mode == "callback_argument") begin
      `checkd(derived_callback::callback_calls, 1);
      `checkd(derived_callback::after_callback, 0);
      `checkd(base_int::constructor_calls, 0);
      `checkd(derived_callback::after_super, 0);
    end
    else if (mode == "multiple_arguments") begin
      `checkd(derived_multi::argument_calls, 1);
      `checkd(base_multi::constructor_calls, 0);
      `checkd(derived_multi::after_super, 0);
    end
    else if (mode == "non_finishing_argument") begin
      `checkd(derived_complete::argument_calls, 1);
      `checkd(base_multi::constructor_calls, 1);
      `checkd(derived_complete::after_super, 1);
    end
    else if (mode == "mixed_arguments") begin
      `checkd(derived_mixed::finish_calls, 1);
      `checkd(derived_mixed::after_finish_sibling, 0);
      `checkd(base_multi::constructor_calls, 0);
      `checkd(derived_mixed::after_super, 0);
    end
    else if (mode == "mixed_arguments_reverse") begin
      `checkd(derived_mixed_reverse::finish_calls, 1);
      `checkd(derived_mixed_reverse::after_finish_sibling, 0);
      `checkd(base_multi::constructor_calls, 0);
      `checkd(derived_mixed_reverse::after_super, 0);
    end
    else if (mode == "writable_sibling") begin
      `checkd(derived_writable::finish_calls, 1);
      `checkd(base_writable::constructor_calls, 0);
      `checkd(derived_writable::after_super, 0);
    end
    else if (mode == "writable_complete") begin
      `checkd(base_writable::constructor_calls, 1);
      `checkd(derived_writable_complete::after_super, 1);
      `checkd(out_value, 7);
    end
    else if (mode == "writable_guarded_complete") begin
      `checkd(derived_writable::finish_calls, 1);
      `checkd(base_writable::constructor_calls, 1);
      `checkd(derived_writable::after_super, 1);
      `checkd(out_value, 1);
    end
    else if (mode == "inout_complete") begin
      `checkd(base_inout_plain::constructor_calls, 1);
      `checkd(derived_inout_plain::after_super, 1);
      `checkd(inout_value, 53);
    end
    else if (mode == "inout_sibling") begin
      `checkd(derived_inout_finish::finish_calls, 1);
      `checkd(base_inout_finish::constructor_calls, 0);
      `checkd(derived_inout_finish::after_super, 0);
    end
    else if (mode == "inout_guarded_complete") begin
      `checkd(derived_inout_finish::finish_calls, 1);
      `checkd(base_inout_finish::constructor_calls, 1);
      `checkd(derived_inout_finish::after_super, 1);
      `checkd(inout_value, 53);
    end
    else if (mode == "ref_sibling") begin
      `checkd(derived_ref::finish_calls, 1);
      `checkd(base_ref::constructor_calls, 0);
      `checkd(derived_ref::after_super, 0);
    end
    else if (mode == "ref_complete") begin
      `checkd(base_ref::constructor_calls, 1);
      `checkd(derived_ref_complete::after_super, 1);
      `checkd(ref_value, 9);
    end
    else if (mode == "ref_complex") begin
      `checkd(derived_ref_complex::finish_calls, 1);
      `checkd(derived_ref_complex::after_finish_index, 0);
      `checkd(base_ref_complex::constructor_calls, 0);
      `checkd(derived_ref_complex::after_super, 0);
    end
    else if (mode == "ref_complex_reverse") begin
      `checkd(derived_ref_complex_reverse::finish_calls, 1);
      `checkd(derived_ref_complex_reverse::after_finish_index, 0);
      `checkd(base_ref_complex::constructor_calls, 0);
      `checkd(derived_ref_complex_reverse::after_super, 0);
    end
    else if (mode == "ref_complex_complete") begin
      `checkd(derived_ref_complex_complete::index_calls, 1);
      `checkd(base_ref_complex::constructor_calls, 1);
      `checkd(derived_ref_complex_complete::after_super, 1);
      `checkd(derived_ref_complex_complete::values[1], 9);
    end
    else if (mode == "ref_complex_index_finish") begin
      `checkd(derived_ref_complex_index_finish::index_calls, 1);
      `checkd(derived_ref_complex_index_finish::after_index, 0);
      `checkd(base_ref_complex::constructor_calls, 0);
      `checkd(derived_ref_complex_index_finish::after_super, 0);
    end
    else if (mode == "ref_queue_complete") begin
      `checkd(derived_ref_queue_complete::index_calls, 1);
      `checkd(base_ref_complex::constructor_calls, 1);
      `checkd(derived_ref_queue_complete::after_super, 1);
      `checkd(derived_ref_queue_complete::values[1], 9);
    end
    else if (mode == "const_ref_sibling") begin
      `checkd(derived_const_ref::finish_calls, 1);
      `checkd(base_const_ref::constructor_calls, 0);
      `checkd(derived_const_ref::after_super, 0);
    end
    else if (mode == "const_ref_complex") begin
      `checkd(derived_const_ref_complex::finish_calls, 1);
      `checkd(derived_const_ref_complex::after_finish_index, 0);
      `checkd(base_const_ref_complex::constructor_calls, 0);
      `checkd(derived_const_ref_complex::after_super, 0);
    end
    else if (mode == "const_ref_complex_reverse") begin
      `checkd(derived_const_ref_complex_reverse::finish_calls, 1);
      `checkd(derived_const_ref_complex_reverse::after_finish_index, 0);
      `checkd(base_const_ref_complex::constructor_calls, 0);
      `checkd(derived_const_ref_complex_reverse::after_super, 0);
    end
    else if (mode == "const_ref_complex_complete") begin
      `checkd(derived_const_ref_complex_complete::index_calls, 1);
      `checkd(base_const_ref_complex::constructor_calls, 1);
      `checkd(base_const_ref_complex::observed, 70);
      `checkd(derived_const_ref_complex_complete::after_super, 1);
    end
    else if (mode == "const_ref_complex_index_finish") begin
      `checkd(derived_const_ref_complex_index_finish::index_calls, 1);
      `checkd(derived_const_ref_complex_index_finish::after_index, 0);
      `checkd(base_const_ref_complex::constructor_calls, 0);
      `checkd(derived_const_ref_complex_index_finish::after_super, 0);
    end
    else if (mode == "constructor_chain") begin
      `checkd(derived_chain::finish_calls, 1);
      `checkd(grandparent_chain::constructor_calls, 0);
      `checkd(parent_chain::after_super, 0);
      `checkd(derived_chain::after_super, 0);
    end
    else if (mode == "default_argument") begin
      `checkd(default_arg_ctor::default_calls, 1);
      `checkd(default_arg_ctor::after_default, 0);
      `checkd(default_arg_ctor::constructor_calls, 0);
    end
    else if (mode == "default_super_argument") begin
      `checkd(default_arg_ctor::default_calls, 1);
      `checkd(default_arg_ctor::after_default, 0);
      `checkd(default_arg_ctor::constructor_calls, 0);
      `checkd(derived_default_arg::after_super, 0);
    end
    if (mode != "writable_complete" && mode != "writable_guarded_complete") `checkd(out_value, 40);
    if (mode != "inout_complete" && mode != "inout_guarded_complete") `checkd(inout_value, 50);
    if (mode != "ref_complete") `checkd(ref_value, 60);
    $write("*-* All Finished *-*\n");
  end
endmodule
