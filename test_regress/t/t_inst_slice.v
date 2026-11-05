// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Varun Koyyalagunta
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef struct {
  logic [6:0] head;
  logic [6:0] tail [2];
} aggregate_t;

class output_entry;
  static logic [6:0] data;
endclass

// bug1015
module t (
    input clk
);

  integer cyc = 0;
  reg [63:0] crc;
  reg [63:0] sum;

  // Take CRC data and apply to testblock inputs
  wire [1:0] i = crc[1:0];
  logic [1:0] o[13:10];

  Test test (  /*AUTOINST*/
      // Outputs
      .o(o  /*[1:0].[3:0]*/),
      // Inputs
      .i(i[1:0])
  );

  // Aggregate outputs into a single result vector
  wire [63:0] result = {32'h0, 6'h0, o[13], 6'h0, o[12], 6'h0, o[11], 6'h0, o[10]};

  // Constant net selections and dynamic variable selections are valid output destinations.
  typedef struct {
    logic [6:0] data;
  } entry_t;
  wire entry_t net_members [3:1];
  entry_t variable_members [3:1];
  wire [6:0] net_slices [3:1][4:1];
  logic [6:0] variable_slices [3:1][1:4];
  wire [31:0] row = 1 + int'(crc[15:14]) % 3;
  selected_output net_output (
      .value(crc[6:0]),
      .pad(net_slices[2][3:2]),
      .member(net_members[2].data)
  );
  selected_output variable_output (
      .value(crc[13:7]),
      .pad(variable_slices[row][2:3]),
      // A packed selection used to compute an unpacked index is an rvalue.
      .member(variable_members[1 + int'(crc[crc[19:14]]) % 3].data)
  );

  // Static class properties permit output connections, including access through a handle.
  output_entry static_member;
  selected_output class_output (
      .value(crc[6:0]),
      .pad(),
      .member(static_member.data)
  );

  // Inputs may select dynamically inside constructors. Output array constructors
  // permit constant net selections and dynamic unpacked variable selections.
  wire [6:0] pattern_net [2];
  logic [6:0] pattern_variable [3:1][2];
  aggregate_t struct_result;
  wire [6:0] input_value = crc[7 * int'(crc[17:16]) +: 7];
  aggregate_echo struct_echo (
      .source('{crc[7 * int'(crc[17:16]) +: 7], '{crc[6:0], crc[13:7]}}),
      .sink(struct_result)
  );
  array_echo pattern_echo (
      .source({crc[7 * int'(crc[17:16]) +: 7], crc[13:7]}),
      .sink('{pattern_net[0], pattern_net[1]})
  );
  array_echo variable_pattern_echo (
      .source('{crc[6:0], crc[13:7]}),
      .sink('{pattern_variable[row][0], pattern_variable[row][1]})
  );
  always @(negedge clk) begin
    if (cyc > 1) begin
      `checkh(net_slices[2][3], crc[6:0]);
      `checkh(net_slices[2][2], ~crc[6:0]);
      `checkh(net_members[2].data, crc[6:0]);
      `checkh(variable_slices[row][2], crc[13:7]);
      `checkh(variable_slices[row][3], ~crc[13:7]);
      `checkh(variable_members[1 + int'(crc[crc[19:14]]) % 3].data, crc[13:7]);
      `checkh(output_entry::data, crc[6:0]);
      `checkh(struct_result.head, input_value);
      `checkh(struct_result.tail[0], crc[6:0]);
      `checkh(struct_result.tail[1], crc[13:7]);
      `checkh(pattern_net[0], input_value);
      `checkh(pattern_net[1], crc[13:7]);
      `checkh(pattern_variable[row][0], crc[6:0]);
      `checkh(pattern_variable[row][1], crc[13:7]);
    end
  end

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x result=%x sum=%x\n", $time, cyc, crc, result, sum);
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
      `define EXPECTED_SUM 64'hb42b2f48a0a9375a
      if (sum !== `EXPECTED_SUM) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test (
    output logic [1:0] o[3:0],
    //but this works
    //logic [N-1:0] o
    input [1:0] i
);

  parameter N = 4;

  logic [1:0] a[3:0];
  initial a = '{2'h0, 2'h1, 2'h2, 2'h3};

  sub sub[N-1:0] (
      .o(o),  // many-to-many
      .a(a),  // many-to-many
      .i(i)
  );  // many-to-one
endmodule

module sub (
    input logic [1:0] i,
    input logic [1:0] a,
    output logic [1:0] o
);
  assign o = i + a;
endmodule

module selected_output (
    input wire [6:0] value,
    output wire [6:0] pad [1:2],
    output wire [6:0] member
);
  assign pad[1] = value;
  assign pad[2] = ~value;
  assign member = value;
endmodule

module aggregate_echo (
    input wire aggregate_t source,
    output wire aggregate_t sink
);
  assign sink = source;
endmodule

module array_echo (
    input wire [6:0] source [2],
    output wire [6:0] sink [2]
);
  assign sink = source;
endmodule
