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
      bins single = values;
      ignore_bins ignored_single = values iff (gate);
      illegal_bins illegal_single = values;
      wildcard bins wild_single = values iff (gate);
      wildcard ignore_bins wild_ignored_single = values;
      wildcard illegal_bins wild_illegal_single = values iff (gate);
    }
  endgroup

  // Array-bin sizes are expressions, independent of the input array expression.
  covergroup cg_sizes(input int count) with function sample (int value);
    cp: coverpoint value {
      bins fixed_size[2] = values;
      bins parameter_size[count] = values;
      bins expression_size[count + 1] = values iff (enabled);
      ignore_bins ignored_size[2] = values;
      illegal_bins illegal_size[2] = values;
      wildcard bins wild_size[2] = values;
      wildcard ignore_bins wild_ignored_size[2] = values;
      wildcard illegal_bins wild_illegal_size[2] = values;
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
      bins parenthesized[] = (values);
      bins nested_parentheses[] = ((values));

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
      bins locator[] = values.find with (item > 3);
      bins locator_parentheses[] = values.find() with (item > 3);
      bins locator_iterator[] = values.find(element) with (element > 3);
      bins locator_indices[] = values.find_index with (item > 3);
      bins unique_values[] = values.unique();
      bins minimum_values[] = values.min();
      bins maximum_values[] = values.max();

      // Casts and assignment patterns preserve the array result type.
      bins type_cast[] = queue_t'(values);
      bins typed_pattern[] = queue_t'{index, index + 1, index + 2};
`ifdef TEST_PATTERN_UNSUP
      bins cast_pattern[] = queue_t'('{index, index + 1});
`endif
      bins unpacked_concat[] = queue_t'({values, other_values});

      // Conditional branches return arrays; parentheses must not start transitions.
      bins conditional[] = enabled ? values : other_values;
      bins parenthesized_conditional[] = (enabled ? values : other_values);
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

  // The remaining A.2.11 bins_or_options alternatives share the expression prefix.
  covergroup cg_productions with function sample (bit [3:0] value, bit gate);
    coverpoint value;
    named_empty: coverpoint value;
    coverpoint gate {
      bins unnamed[] = {0, 1};
    }
    [3:0] implicit_type: coverpoint value iff (gate) {
      bins gated_point[] = {1, 2};
    }
    bit [3:0] typed: coverpoint value {
      option.at_least = 2;
      type_option.weight = 1;
      bins value_single = {1};
      bins value_list[] = {1, 2, 3};
      bins value_range[2] = {[1 : 5]};
      bins open_lower[] = {[$ : 2]};
      bins open_upper[] = {[13 : $]};
      bins open_both[] = {[$ : $]};
      bins mixed[] = {1, [3 : 5], 7, [9 : 11]};
      bins listed_iff[] = {1, 2} iff (gate);
      bins listed_with[] = {1, 2} with (item > 1);
      bins listed_with_iff[2] = {[0 : 7]} with (item > 1) iff (gate);
      ignore_bins ignored[] = {1, 2} with (item == 1) iff (gate);
      illegal_bins illegal[2] = {3, 4} with (item == 3) iff (gate);
      wildcard bins wild[] = {4'b1???} with (item > 8) iff (gate);
      wildcard ignore_bins wild_ignored[2] = {4'b01??} with (item == 4) iff (gate);
      wildcard illegal_bins wild_illegal = {4'b00??} with (item == 0) iff (gate);
      ignore_bins ignored_plain[] = {1, 2};
      illegal_bins illegal_plain[2] = {3, 4} iff (gate);
      wildcard bins wild_plain[] = {4'b1???};
      wildcard ignore_bins wild_ignored_plain[2] = {4'b01??} iff (gate);
      wildcard illegal_bins wild_illegal_plain = {4'b00??};
    }
    named: coverpoint value {
      bins named_single = named with (item > 1);
      bins named_array[] = named with (item > 1) iff (gate);
      bins named_sized[2] = named with (item > 1);
      ignore_bins named_ignored[] = named with (item == 2) iff (gate);
      illegal_bins named_illegal[2] = named with (item == 3);
      wildcard bins named_wild[] = named with (item > 8) iff (gate);
      wildcard ignore_bins named_wild_ignored = named with (item == 4);
      wildcard illegal_bins named_wild_illegal[2] = named with (item == 0) iff (gate);
    }
    transitions: coverpoint value {
      bins single = (1 => 2);
      bins array[] = (1 => 2), (3 => 4 => 5);
      bins lists[] = (1, 2 => 3, 4);
      ignore_bins ignored = (5 => 6);
      ignore_bins ignored_array[] = (7 => 8);
      illegal_bins illegal = (9 => 10);
      illegal_bins illegal_array[] = (11 => 12);
    }
    defaults: coverpoint value {
      bins explicit_value = {1};
      bins remaining = default;
    }
    default_array: coverpoint value {
      bins remaining[] = default;
    }
    default_sized: coverpoint value {
      bins remaining[2] = default;
    }
    default_ignore: coverpoint value {
      ignore_bins remaining = default;
    }
    default_illegal: coverpoint value {
      illegal_bins remaining = default;
    }
  endgroup

`ifdef TEST_PARSE_UNSUP
  // These forms diagnose during parsing; isolate them from lowering diagnostics.
  covergroup cg_parse_unsup with function sample (bit [3:0] value, bit gate);
    transitions: coverpoint value {
      bins gated[] = (1 => 2) iff (gate);
      ignore_bins ignored_gated = (3 => 4) iff (gate);
      illegal_bins illegal_gated[] = (5 => 6) iff (gate);
      wildcard bins wild = (1 => 2);
      wildcard bins wild_array[] = (1 => 2), (3 => 4) iff (gate);
      wildcard ignore_bins wild_ignored[] = (5 => 6);
      wildcard illegal_bins wild_illegal = (7 => 8) iff (gate);
    }
    defaults: coverpoint value {
      bins gated = default iff (gate);
      ignore_bins ignored_gated[] = default iff (gate);
      illegal_bins illegal_gated[2] = default iff (gate);
      bins sequence_bin = default sequence;
      bins sequence_gated = default sequence iff (gate);
      ignore_bins ignored_sequence = default sequence;
      ignore_bins ignored_sequence_gated = default sequence iff (gate);
      illegal_bins illegal_sequence = default sequence;
      illegal_bins illegal_sequence_gated = default sequence iff (gate);
    }
  endgroup
  cg_parse_unsup parse_cov = new;
`endif

  cg_productions productions_cov = new;
  cg_kinds kinds_cov = new;
  cg_sizes sizes_cov = new(2);
  cg_inputs inputs_cov = new(values, dynamic_values, fixed_values);
  cg_expressions expressions_cov = new;
endmodule
