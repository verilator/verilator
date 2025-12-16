// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifndef LAST_CYC
`define LAST_CYC 9
`endif

`ifndef NUM_SUBS
`define NUM_SUBS 4
`endif


module t (/*AUTOARG*/
          // Inputs
          clk
          );
  input clk;

  int cyc;
  logic [`NUM_SUBS - 1:0] x;
  initial cyc = 0;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == `LAST_CYC) begin
      if (~|x) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  for (genvar i = 0; i < `NUM_SUBS; i++) begin : gen_loop
    int loop_cyc;
    always_comb loop_cyc = cyc + i;
    sub #(
      .data_t (pkg::some_struct_t)
    )
    the_sub (
      .a (loop_cyc[i%32]),
      .b (loop_cyc[(i+1)%32]),
      .x (x[i]),
      .out_2d_unpacked (),
      .data (),
      .cyc (loop_cyc),
      .clk
    );
  end

  intf
  the_intf_a (.*),
  the_intf_b (.*);

  for (genvar m = 0; m < 4; m++) begin : gen_intf_loop
    always_comb begin
      the_intf_a.data[m] = cyc[7:0] + m + 7'd1;
      the_intf_b.data[m] = cyc[7:0] + m + 7'd2;
    end
  end

endmodule

package pkg;
  typedef struct packed {
    logic field_a;
    logic [5:0] field_b;
    logic [9:0] field_c;
  } some_sub_struct_t;

  typedef struct packed {
    logic foo;
    logic [3:0] [31:0] bar;
    logic [15:0] baz;
    logic [127:0] qux;
    some_sub_struct_t sub_struct;
  } some_struct_t;

  parameter some_sub_struct_t SUB_ONES = '1;
  parameter some_sub_struct_t SUB_ZEROS = '0;
endpackage

module sub #(
  parameter type data_t = bit
)(
  input a,
  input b,
  output logic x,
  output out_2d_unpacked [3][4],
  output data_t data,
  input int cyc,
  input clk
);
  pkg::some_struct_t the_struct;
  pkg::some_struct_t the_structs [3:0];
  pkg::some_struct_t [2:0] the_packed_structs;

  typedef struct packed {
    logic abc;
    logic def;
    logic xyz;
  } some_struct_t;
  some_struct_t the_local_struct;
  localparam some_struct_t const_struct = 3'b101;
  typedef some_struct_t typedefed_struct_t;
  typedefed_struct_t the_typedefed_struct;

  typedef struct {
    logic field_a;
    logic field_b;
    logic field_c;
  } some_unpacked_struct_t;
  some_unpacked_struct_t the_local_unpacked_struct;

  typedef union packed {
    struct packed {
      logic [7:0] field_0;
    } union_a;
    struct packed {
      logic [3:0] field_1;
      logic [3:0] field_2;
    } union_b;
    struct packed {
      logic [1:0] field_3;
      logic [5:0] field_4;
    } union_c;
  } some_union_t;
  some_union_t the_local_union;

  typedef logic [1:0] [31:0] logic_array_t;
  typedef logic [1:0] [31:0] logic_array_2_t;
  logic_array_t the_logic_array;
  logic_array_2_t the_other_logic_array;
  logic [15:0] the_unpacked_array [5];
  logic the_2d_unpacked [3][4];

  typedef logic [3:0] four_bit_t;
  typedef four_bit_t [1:0] two_fours_t;
  localparam two_fours_t two_fours = 8'hab;
  two_fours_t two_fours_var;

  always_ff @(posedge clk) begin
    x <= a ^ b;
    the_struct <= '{
      foo : cyc[0],
      bar : '{cyc, cyc+1, cyc+2, cyc+3},
      baz : cyc[15:0],
      qux : 128'(cyc),
      sub_struct : '{
        field_a : cyc[0],
        field_b : cyc[5:0],
        field_c : cyc[9:0]
      }
    };
    for (int i = 0; i < 4; i++) the_structs[i] <= {$bits(pkg::some_struct_t){cyc[i]}};
    the_local_struct <= cyc[2:0];
    the_typedefed_struct <= cyc[3:1];
    the_local_unpacked_struct <= '{
      field_a : cyc[0],
      field_b : cyc[1],
      field_c : cyc[2]
    };
    the_local_union <= cyc[7:0];
    for (int i = 0; i < 2; i++) begin
      the_logic_array[i] <= cyc + i;
      the_other_logic_array[i] <= cyc + i + 123;
    end
    for (int i = 0; i < 5; i++) the_unpacked_array[i] <= cyc[15:0];
    for (int i = 0; i < 3; i++)
      for (int j = 0; j < 4; j++) begin
        the_2d_unpacked [i][j] <= ~(cyc[i] ^ cyc[j]);
        out_2d_unpacked [i][j] <= cyc[i] ^ cyc[j];
      end
  end

  always_comb data = the_struct;
endmodule

interface intf
  (input wire clk);
  logic [3:0] [7:0] data;
  int data_typed;
  always_comb data_typed = data;
endinterface
