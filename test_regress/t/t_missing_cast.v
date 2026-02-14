// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module SubSimple #(
  parameter type data_type,
  parameter int depth,
  parameter int init_value = -1
) (
  input data_type sink,
  output data_type source
);
  data_type the_data [depth+1] = '{depth+1{~data_type'(init_value)}};
  if (depth < 0) begin
    $fatal;
  end else if (depth == 0) begin
    always_comb begin
      source = sink;
    end
  end else if (depth == 1) begin
  end else begin
    always_comb begin
      source = the_data[depth];
    end
  end
endmodule

module SubSharded #(
  parameter int DATA_WIDTH = 128,
  parameter int NUM_SHARDS = 8,
  parameter int depth
) (
  input logic [DATA_WIDTH-1:0] sink,
  output logic [DATA_WIDTH-1:0] source
);
  localparam int SHARD_WIDTH = 16;
  for (genvar g = 0; g < NUM_SHARDS; g++) begin
    localparam int data_offset = g * SHARD_WIDTH;
    localparam int local_data_width = 16;
    SubSimple #(
      .data_type (logic [local_data_width-1:0]),
      .depth (depth),
      .init_value (g)
    ) shardedPipeline (
      .sink (sink[data_offset+:local_data_width]),
      .source (source[data_offset+:local_data_width])
    );
  end
endmodule

typedef struct packed {
  logic [127:0] foo;
  logic [1:0]            bar;
} struct_t;

module SampleStruct (
  input  struct_t   [4-1:0]                                             input_struct
);
  initial begin
    #1;
    $display("---> %x", input_struct[3].foo);
    if (input_struct[3].foo != 'hfff8fff9fffafffbfffcfffdfffeffff) $stop;
  end
  bit blargh /*verilator public*/ = '0;
endmodule

module Thing (
  input logic select
);
  struct_t [4-1:0] input_struct_a;
  struct_t [4-1:0] other_struct;
  struct_t [4-1:0] input_struct_b;
  struct_t [4-1:0] input_struct_c;
  always_comb begin
    if (select) begin
      input_struct_a = 'x;
      other_struct[1] = input_struct_c[0];
    end else begin
      input_struct_a = input_struct_b;
      other_struct = '0;
    end
  end
  parameter int depth_other[4] = '{0, 0, 1, 1};
  parameter int depth[4] = '{1, 1, 2, 8};
  for (genvar dir = 0; dir < 4; dir++) begin
    SubSimple #(
      .data_type(logic [1:0]),
      .depth (depth[dir])
    ) subBar (
      .sink ('0),
      .source (input_struct_b[dir].bar)
    );
    SubSimple #(
      .data_type(logic [1:0]),
      .depth (depth_other[dir])
    ) subBarOther (
      .sink (input_struct_b[dir].bar),
      .source (input_struct_c[dir].bar)
    );
    SubSharded #(
      .depth (depth[dir])
    ) subFoo (
      .sink('0),
      .source (input_struct_b[dir].foo)
    );
    SubSharded #(
      .depth(depth_other[dir])
    ) subFooOther (
      .sink (input_struct_b[dir].foo),
      .source (input_struct_c[dir].foo)
    );
  end
  SampleStruct sampleStruct (
    .input_struct (input_struct_a)
  );
endmodule

module t ();
  logic select;
  Thing thing (
    .select
  );
endmodule
