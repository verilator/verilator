// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Varun Koyyalagunta
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct packed {
  logic [2:0] upper;
  logic [3:0] lower;
} struct_t;
typedef struct_t struct_alias_t;
typedef union packed {
  logic [6:0] bits;
  struct_t fields;
} union_t;
typedef union_t union_alias_t;
typedef enum logic [9:3] {
  ZERO = 7'h00,
  ONES = 7'h7f
} enum_t;
typedef enum_t enum_alias_t;
/* verilator lint_off ASCRANGE */
typedef logic [2:3][5:3] matrix_t;
/* verilator lint_on ASCRANGE */
typedef struct_t [3:2] struct_array_t;

typedef struct packed {logic x;} nested_named_t;

typedef struct packed {
  struct packed {logic x;} nested_anonymous;
  nested_named_t nested_named;
  logic [1:0] x;
} nibble_t;

module t (
    input clk
);

  integer cyc = 0;
  logic [63:0] crc;
  logic [63:0] sum;

  // Take CRC data and apply to testblock inputs
  nibble_t [7:0] in;
  assign in = crc[31:0];

  nibble_t [7:0] out;

  Test test (
      .out0({out[1], out[0]}),
      .out1({{out[5], out[4]}, {out[3], out[2]}}),
      .out2(out[6]),
      .out3(out[7]),
      .clk(clk),
      .in0(in[0]),
      .in1(in[1]),
      .in2({in[5], in[4], in[3], in[2]}),
      .in3({in[7], in[6]})
  );

  inout_types_check inout_check (.clk(clk));

  // Aggregate outputs into a single result vector
  wire [63:0] result = {32'h0, out};

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
    if (cyc == 0) begin
      // Setup
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= '0;
    end
    else if (cyc < 10) begin
      sum <= '0;
    end
    else if (cyc < 90) begin
    end
    else if (cyc == 99) begin
      $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
      if (crc !== 64'hc77bb9b3784ea091) $stop;
      // What checksum will we end up with (above print should match)
      `define EXPECTED_SUM 64'h4afe43fb79d7b71e
      if (sum !== `EXPECTED_SUM) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test (
    // Outputs
    output nibble_t [1:0] out0,
    output nibble_t [1:0] out1[2],
    output nibble_t out2,
    output nibble_t out3,
    // Inputs
    input clk,
    input nibble_t in0,
    input nibble_t in1,
    input nibble_t [3:0] in2,
    input nibble_t in3[2]
);  /*verilator hier_block*/


  always @(posedge clk) begin
    {out3, out2, out1[0], out1[1], out0} <= {in3[0], in3[1], in2, in1, in0};
  end

endmodule

module inout_types_drive (
    input logic [6:0] en,
    input logic [6:0] data,
    inout wire scalar_pad,
    inout wire struct packed {
      logic [2:0] upper;
      logic [3:0] lower;
    } struct_pad,
    inout wire struct_alias_t struct_alias_pad,
    inout wire union packed {
      logic [6:0] bits;
      struct_t fields;
    } union_pad,
    inout wire union_alias_t union_alias_pad,
    inout wire enum_t enum_pad,
    inout wire enum_alias_t enum_alias_pad,
    inout wire matrix_t matrix_pad,
    inout wire struct_array_t struct_array_pad,
    output wire scalar_q,
    output wire [6:0] struct_q,
    output wire [6:0] struct_alias_q,
    output wire [6:0] union_q,
    output wire [6:0] union_alias_q,
    output wire [6:0] enum_q,
    output wire [6:0] enum_alias_q,
    output wire [5:0] matrix_q,
    output wire [13:0] struct_array_q
);
  /* verilator hier_block */
  assign scalar_pad = en[0] ? data[0] : 1'bz;
  for (genvar i = 0; i < 7; ++i) begin
    assign struct_pad[i] = en[i] ? data[i] : 1'bz;
    assign struct_alias_pad[i] = en[i] ? data[i] : 1'bz;
    assign union_pad[i] = en[i] ? data[i] : 1'bz;
    assign union_alias_pad[i] = en[i] ? data[i] : 1'bz;
    assign enum_pad[i+3] = en[i] ? data[i] : 1'bz;
    assign enum_alias_pad[i+3] = en[i] ? data[i] : 1'bz;
    assign struct_array_pad[2][i] = en[i] ? data[i] : 1'bz;
    assign struct_array_pad[3][i] = en[i] ? ~data[i] : 1'bz;
  end
  for (genvar i = 2; i <= 3; ++i) begin
    for (genvar j = 3; j <= 5; ++j) begin
      localparam int BIT = (3 - i) * 3 + j - 3;
      assign matrix_pad[i][j] = en[BIT] ? data[BIT] : 1'bz;
    end
  end
  assign scalar_q = scalar_pad;
  assign struct_q = struct_pad;
  assign struct_alias_q = struct_alias_pad;
  assign union_q = union_pad;
  assign union_alias_q = union_alias_pad;
  assign enum_q = enum_pad;
  assign enum_alias_q = enum_alias_pad;
  assign matrix_q = matrix_pad;
  assign struct_array_q = struct_array_pad;
endmodule

module inout_types_check (input clk);
  logic [6:0] en = '0;
  logic [6:0] data = 7'h53;
  wire [6:0] external_data = ~data;
  wire [6:0] expected = (en & data) | (~en & external_data);
  wire scalar_pad;
  wire struct_t struct_pad;
  wire struct_alias_t struct_alias_pad;
  wire union_t union_pad;
  wire union_alias_t union_alias_pad;
  wire enum_t enum_pad;
  wire enum_alias_t enum_alias_pad;
  wire matrix_t matrix_pad;
  wire struct_array_t struct_array_pad;
  wire scalar_q;
  wire [6:0] struct_q;
  wire [6:0] struct_alias_q;
  wire [6:0] union_q;
  wire [6:0] union_alias_q;
  wire [6:0] enum_q;
  wire [6:0] enum_alias_q;
  wire [5:0] matrix_q;
  wire [13:0] struct_array_q;

  inout_types_drive dut (.*);

  // External drivers own precisely the bits disabled inside the library.
  assign scalar_pad = en[0] ? 1'bz : external_data[0];
  for (genvar i = 0; i < 7; ++i) begin
    assign struct_pad[i] = en[i] ? 1'bz : external_data[i];
    assign struct_alias_pad[i] = en[i] ? 1'bz : external_data[i];
    assign union_pad[i] = en[i] ? 1'bz : external_data[i];
    assign union_alias_pad[i] = en[i] ? 1'bz : external_data[i];
    assign enum_pad[i+3] = en[i] ? 1'bz : external_data[i];
    assign enum_alias_pad[i+3] = en[i] ? 1'bz : external_data[i];
    assign struct_array_pad[2][i] = en[i] ? 1'bz : external_data[i];
    assign struct_array_pad[3][i] = en[i] ? 1'bz : ~external_data[i];
  end
  for (genvar i = 2; i <= 3; ++i) begin
    for (genvar j = 3; j <= 5; ++j) begin
      localparam int BIT = (3 - i) * 3 + j - 3;
      assign matrix_pad[i][j] = en[BIT] ? 1'bz : external_data[BIT];
    end
  end

  initial begin
    // Check source indices as well as values; whole-vector transfers can hide
    // a wrapper that changes the declared bounds or direction.
    `checkh($left(dut.matrix_pad, 1), 2);
    `checkh($right(dut.matrix_pad, 1), 3);
    `checkh($left(dut.matrix_pad, 2), 5);
    `checkh($right(dut.matrix_pad, 2), 3);
    `checkh($left(dut.struct_array_pad), 3);
    `checkh($right(dut.struct_array_pad), 2);
    `checkh($left(dut.enum_pad), 9);
    `checkh($right(dut.enum_pad), 3);
  end

  // Cycle through all bits disabled, then each bit enabled individually.
  always @(negedge clk) begin
    en <= {en[5:0], ~|en};
    data <= {data[5:0], data[6] ^ data[5]};
  end

  always @(posedge clk) begin
    `checkh(scalar_pad, expected[0]);
    `checkh(struct_pad, expected);
    `checkh(struct_alias_pad, expected);
    `checkh(union_pad, expected);
    `checkh(union_alias_pad, expected);
    `checkh(enum_pad, expected);
    `checkh(enum_alias_pad, expected);
    `checkh(matrix_pad, expected[5:0]);
    `checkh(struct_array_pad, {~expected, expected});
    `checkh(scalar_q, expected[0]);
    `checkh(struct_q, expected);
    `checkh(struct_alias_q, expected);
    `checkh(union_q, expected);
    `checkh(union_alias_q, expected);
    `checkh(enum_q, expected);
    `checkh(enum_alias_q, expected);
    `checkh(matrix_q, expected[5:0]);
    `checkh(struct_array_q, {~expected, expected});
  end
endmodule
