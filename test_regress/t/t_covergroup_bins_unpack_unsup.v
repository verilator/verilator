// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

package queue_pkg;
  typedef int queue_t[$];
  typedef int dynamic_t[];
  typedef int fixed_t[3];

  queue_t values = '{3, 7, 11};

  function automatic queue_t get_values(input int offset = 0);
    return '{3 + offset, 7 + offset, 11 + offset};
  endfunction
endpackage

module t;
  import queue_pkg::queue_t;
  import queue_pkg::dynamic_t;
  import queue_pkg::fixed_t;

  class base_t;
    queue_t inherited_values = '{3, 7, 11};
  endclass

  class source_t extends base_t;
    queue_t values = '{3, 7, 11};
    static queue_t static_values = '{3, 7, 11};

    function queue_t get_values(input int offset = 0);
      return '{3 + offset, 7 + offset, 11 + offset};
    endfunction

    covergroup cg_members with function sample (int value);
      cp: coverpoint value {
        bins this_member[] = this.values;
        bins inherited_member[] = inherited_values;
      }
    endgroup

    function new();
      cg_members = new;
    endfunction
  endclass

  source_t source = new;
  queue_t values = '{3, 7, 11};
  queue_t other_values = '{5, 9, 13};
  dynamic_t dynamic_values = '{3, 7, 11};
  fixed_t fixed_values = '{3, 7, 11};
  queue_t indexed_values[3] = '{'{1}, '{3, 7}, '{11}};
  queue_t associative_values[int];
  int index = 1;
  int mask = 3;
  bit enabled = 1;

  function automatic queue_t get_values(input int offset = 0);
    return queue_pkg::get_values(offset);
  endfunction

  function automatic source_t get_source();
    return source;
  endfunction

  // All bins keywords, wildcard variants, and optional iff clauses.
  covergroup cg_kinds with function sample (int value, bit gate);
    cp: coverpoint value {
      bins normal[] = values;
      bins normal_iff[] = values iff (gate);
      ignore_bins ignored[] = values;
      ignore_bins ignored_iff[] = values iff (gate);
      illegal_bins illegal[] = values;
      illegal_bins illegal_iff[] = values iff (gate);
      wildcard bins wild_normal[] = values;
      wildcard bins wild_normal_iff[] = values iff (gate);
      wildcard ignore_bins wild_ignored[] = values;
      wildcard ignore_bins wild_ignored_iff[] = values iff (gate);
      wildcard illegal_bins wild_illegal[] = values;
      wildcard illegal_bins wild_illegal_iff[] = values iff (gate);
      // Set expressions also permit one bin or a fixed number of bins.
      bins single = values;
      bins sized[2] = values iff (gate);
      ignore_bins single_ignored = values iff (gate);
      ignore_bins sized_ignored[2] = values;
      illegal_bins single_illegal = values;
      illegal_bins sized_illegal[2] = values iff (gate);
      wildcard bins single_wild = values iff (gate);
      wildcard bins sized_wild[2] = values;
      wildcard ignore_bins single_wild_ignored = values;
      wildcard ignore_bins sized_wild_ignored[2] = values iff (gate);
      wildcard illegal_bins single_wild_illegal = values iff (gate);
      wildcard illegal_bins sized_wild_illegal[2] = values;
    }
    gate_cp: coverpoint gate;
    cx: cross cp, gate_cp {
      bins selected = binsof (cp.single);
    }
  endgroup

  // Constructor inputs: queues, dynamic arrays, and fixed arrays.
  covergroup cg_inputs(
      input queue_t queue_arg, input dynamic_t dynamic_arg, input fixed_t fixed_arg
  ) with function sample (
      int value
  );
    cp: coverpoint value {
      bins queue_input[] = queue_arg;
      bins dynamic_input[] = dynamic_arg;
      bins fixed_input[] = fixed_arg;
    }
  endgroup

  covergroup cg_expressions with function sample (int value);
    cp: coverpoint value {
      // Primary expressions and every scope/member-access form.
      bins dynamic_array[] = dynamic_values;
      bins fixed_array[] = fixed_values;
      bins package_scope[] = queue_pkg::values;
      bins class_scope[] = source_t::static_values;
      bins hierarchical[] = t.values;
      bins class_member[] = source.values;

      // Element selection returns an array; a queue slice is itself an array.
      bins indexed[] = indexed_values[index];
      bins associative_index[] = associative_values[index];
      bins slice[] = values[0:1];
      bins slice_to_end[] = values[1:$];
      bins prefix_increment[] = indexed_values[++index];
      bins postfix_increment[] = indexed_values[index++];
      bins prefix_decrement[] = indexed_values[--index];
      bins postfix_decrement[] = indexed_values[index--];

      // Calls, argument syntax, chained calls, and array locator methods.
      bins function_call[] = get_values();
      bins function_arguments[] = get_values(index + 1);
      bins named_arguments[] = get_values(.offset(index));
      bins package_function[] = queue_pkg::get_values(index);
      bins method_call[] = source.get_values(index);
      bins chained_call[] = get_source().get_values(index);
      bins unique_values[] = values.unique();
      bins minimum_values[] = values.min();
      bins maximum_values[] = values.max();

      // Casts and assignment patterns preserve the array result type.
      bins type_cast[] = queue_t'(values);
      bins typed_pattern[] = queue_t'{index, index + 1, index + 2};
      bins unpacked_concat[] = queue_t'({values, other_values});

      // Conditional branches return arrays; parentheses must not start transitions.
      bins conditional[] = enabled ? values : other_values;
      bins nested_conditional[] = enabled ? (index != 0 ? values : other_values) : values;

      // Operators at the expression root, including the ambiguous brace prefix.
      bins arithmetic_condition[] = index + 2 * 3 - 1 > 0 ? values : other_values;
      bins shift_condition[] = mask << index != 0 ? values : other_values;
      bins logical_condition[] = enabled && index != 0 || mask == 0 ? values : other_values;
      bins reduction_condition[] = ^mask ? values : other_values;
      bins inside_condition[] = index inside {0, [2 : 3]} ? values : other_values;
      bins signed_condition[] = $signed(mask) < 0 ? values : other_values;
      bins sized_cast_condition[] = 3'(index) != 0 ? values : other_values;
      bins streaming_condition[] = int'({<<{mask}}) != 0 ? values : other_values;
    }
  endgroup
  covergroup cg_default with function sample (int value);
    cp: coverpoint value {
      bins remaining[2] = default;
    }
  endgroup

  covergroup cg_concat;
    cp: coverpoint 1'b0 {
      /* verilator lint_off WIDTHEXPAND */
      bins concat_condition[] = {1'b1 + 1'b1} == 2'b10 ? values : other_values;
      /* verilator lint_on WIDTHEXPAND */
    }
  endgroup

  // Packed arrays are legal, including constants, but must not become one scalar bin.
  typedef logic [2:1][4:0] packed_t;
  packed_t packed_values;
  localparam packed_t PACKED_VALUES = {5'd3, 5'd7};
  typedef logic [4:0] vector_t;
  vector_t vector_values;
  typedef real real_array_t[2];
  real_array_t real_values = '{1.5, 2.5};
  typedef enum {ONE = 1, TWO = 2} enum_t;
  enum_t enum_values[$] = '{ONE, TWO};
  enum_t enum_value;
  real real_value;
  covergroup cg_types;
    cp: coverpoint packed_values[1] {
      bins packed_array[] = packed_values;
      bins packed_constant[] = PACKED_VALUES;
      bins packed_single = PACKED_VALUES;
      bins packed_sized[2] = PACKED_VALUES;
      bins vector_array[] = vector_values;
      bins brace_select[] = {4'd1, 4'd2}[3:0];
      bins real_array[] = real_values;
    }
    cp_enum: coverpoint enum_value {
      bins same_enum[] = enum_values;
    }
    cp_real: coverpoint real_value {
      bins integer_array[] = values;
    }
  endgroup
  cg_types types_cov = new;

  cg_kinds kinds_cov = new;
  cg_inputs inputs_cov = new(values, dynamic_values, fixed_values);
  cg_expressions expressions_cov = new;
  cg_default default_cov = new;
  cg_concat concat_cov = new;
endmodule
