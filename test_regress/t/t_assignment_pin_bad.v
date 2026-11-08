// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module test1 (
    input logic b
);
  logic do_something;
  assign do_something = b;
endmodule

module test2 (
    input bit b[2]
);
  bit do_something[2];
  assign do_something = b;
endmodule

typedef logic [2:0] vector_t;
typedef logic [6:0] array_t[1:2];
typedef logic [6:0] dynamic_t[];
typedef logic [6:0] queue_t[$];
typedef struct {
  logic [6:0] head;
  array_t tail;
} aggregate_t;

module t (
    input logic a[2],  // unpacked array
    input logic [5:0] cyc
);

  logic b[2];

  assign b = a;

  test1 i_test1 (.b);
  test2 i_test2 (.b);

  // Inout destinations require constant packed and unpacked selections.
  tri1 [1:0] pin_index;
  assign pin_index = cyc[0] ? cyc[2:1] : 2'bz;
  wire pin_pad[3:1];
  wire [6:0] packed_pad;
  inout_port indexed_array (.pad(pin_pad[1+int'(pin_index)%3]));
  inout_port indexed_bit (.pad(packed_pad[cyc[2:0]]));
  inout_port #(.T(vector_t)) indexed_part (.pad(packed_pad[cyc[2:0]+:3]));

  // A runtime system function is nonconstant even without variable references.
  inout_port time_bit (.pad(packed_pad[3'($time%7)]));

  // Output destinations distinguish unpacked nets from variables, but packed
  // selections must be constant for both (IEEE 1800-2023 10.2, A.8.5).
  logic [6:0] variable_pad;
  output_port indexed_bit_output (.pad(packed_pad[cyc[2:0]]));
  output_port indexed_array_output (.pad(pin_pad[1+int'(cyc[2:0])%3]));
  output_port time_array_output (.pad(pin_pad[1+int'($time%3)]));
  output_port indexed_variable_bit_output (.pad(variable_pad[cyc[2:0]]));

  // Both sides of a concatenation must satisfy the destination selection rules.
  inout_port #(.T(vector_t)) indexed_concat_lhs (.pad({packed_pad[cyc[2:0]], packed_pad[1:0]}));
  inout_port #(.T(vector_t)) indexed_concat_rhs (.pad({packed_pad[1:0], packed_pad[cyc[2:0]]}));

  // Constant slices must not hide dynamic selections of the containing net array.
  wire [6:0] slice_pad[3:1][4:1];
  output_port #(.T(array_t)) indexed_slice_output (.pad(slice_pad[1+int'(cyc[1:0])%3][3:2]));
  inout_port #(.T(array_t)) indexed_slice_io (.pad(slice_pad[1+int'(cyc[1:0])%3][3:2]));

  // Unpacked members can hide dynamic selections, including below a slice.
  typedef struct {
    logic data;
    logic [6:0] values[4:1];
  } entry_t;
  wire entry_t struct_pad[3:1];
  output_port indexed_member_output (.pad(struct_pad[1+int'(cyc[1:0])%3].data));
  inout_port indexed_member_io (.pad(struct_pad[1+int'(cyc[1:0])%3].data));
  output_port #(
      .T(array_t)
  ) indexed_member_slice_output (
      .pad(struct_pad[1+int'(cyc[1:0])%3].values[3:2])
  );

  // Aggregate destinations must inspect each item, including nested patterns.
  wire [14:0] pattern_bits;
  output_port #(.T(array_t)) pattern_output (.pad('{pattern_bits[cyc[3:0]+:7], pattern_bits[6:0]}));
  output_port #(
      .T(array_t)
  ) net_pattern_output (
      .pad('{slice_pad[1][1], slice_pad[1+int'(cyc[1:0])%3][1]})
  );
  output_port #(
      .T(aggregate_t)
  ) nested_pattern_output (
      .pad('{pattern_bits[6:0], '{slice_pad[1][1], slice_pad[1+int'(cyc[1:0])%3][1]}})
  );
  output_port #(
      .T(dynamic_t)
  ) dynamic_pattern_output (
      .pad('{pattern_bits[6:0], pattern_bits[cyc[3:0]+:7]})
  );
  output_port #(
      .T(queue_t)
  ) queue_pattern_output (
      .pad('{slice_pad[1][1], slice_pad[1+int'(cyc[1:0])%3][1]})
  );

  // Inout connections are not assignment-like contexts, so supply the pattern type.
  inout_port #(
      .T(array_t)
  ) pattern_io (
      .pad(array_t'{pattern_bits[6:0], pattern_bits[cyc[3:0]+:7]})
  );
  inout_port #(
      .T(aggregate_t)
  ) nested_pattern_io (
      .pad(aggregate_t'{pattern_bits[6:0], '{slice_pad[1][1], slice_pad[1+int'(cyc[1:0])%3][1]}})
  );

  // Streams must inspect packed selections, multiple items, and nested array selections.
  output_port stream_left_bit (.pad({<<{variable_pad[cyc[2:0]]}}));
  output_port #(.T(vector_t)) stream_left_part (.pad({<<2{packed_pad[cyc[2:0]+:3]}}));
  output_port #(
      .T(vector_t)
  ) stream_right_concat (
      .pad({>>{packed_pad[1:0], packed_pad[cyc[2:0]]}})
  );
  output_port stream_nested (.pad({<<{{>>{pin_pad[1+int'($time%3)]}}}}));

  // Calls are not valid destinations. Their read operands must not be mistaken
  // for destination selections; report the dynamic selection after each call.
  function automatic logic selected_value(input logic value);
    return value;
  endfunction
  output_port #(
      .T(logic [1:0])
  ) function_concat_output (
      .pad({selected_value(variable_pad[cyc[2:0]]), variable_pad[cyc[2:0]]})
  );

  logic queue_pad[2][$];
  output_port #(
      .T(logic [1:0])
  ) method_concat_output (
      .pad({queue_pad[variable_pad[cyc[2:0]]].pop_front(), variable_pad[cyc[2:0]]})
  );

  // Output connections imply continuous assignments, which cannot write dynamic
  // array elements or non-static class properties (IEEE 1800-2023 6.21).
  logic [6:0] associative_members[int];
  net_output_port associative_output (.pad(associative_members[int'(variable_pad[cyc[2:0]])]));
  output_port #(.T(logic [6:0])) associative_constant_output (.pad(associative_members[0]));

  logic [6:0] queue_members[$] = '{0, 0};
  net_output_port queue_output (.pad(queue_members[{31'b0, variable_pad[cyc[2:0]]}]));
  output_port #(.T(logic [6:0])) queue_constant_output (.pad(queue_members[0]));
  output_port #(.T(logic [6:0])) queue_back_output (.pad(queue_members[$]));

  logic [6:0] dynamic_members[];
  output_port #(.T(logic [6:0])) dynamic_output (.pad(dynamic_members[cyc]));
  output_port #(.T(logic [6:0])) dynamic_constant_output (.pad(dynamic_members[0]));

  logic [6:0] wildcard_members [*];
  output_port #(.T(logic [6:0])) wildcard_output (.pad(wildcard_members[cyc]));

  class output_entry;
    logic [6:0] data;
  endclass
  output_entry class_members[2];
  initial begin
    class_members[0] = new;
    class_members[1] = new;
  end
  net_output_port class_output (.pad(class_members[variable_pad[cyc[2:0]]].data));
  output_port #(.T(logic [6:0])) class_constant_output (.pad(class_members[0].data));
endmodule

// Only the port direction and type matter to these elaboration-time diagnostics.
module output_port #(
    parameter type T = logic
) (
    output T pad
);
endmodule

module inout_port #(
    parameter type T = logic
) (
    inout wire T pad
);
endmodule

module net_output_port (
    output wire [6:0] pad
);
endmodule
