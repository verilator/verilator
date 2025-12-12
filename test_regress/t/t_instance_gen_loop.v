// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t (/*AUTOARG*/
          // Inputs
          clk
          );
  input clk;

  int cyc;
  logic [3:0] x;
  initial cyc = 0;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 9) begin
      if (~|x) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  for (genvar i = 0; i < 4; i++) begin : gen_loop
    int loop_cyc;
    always_comb loop_cyc = cyc + i;
    some_submodule_we_do_not_want_replicated
    the_sub (
      .a (loop_cyc[i]),
      .b (loop_cyc[i+1]),
      .x (x[i]),
      // NOCOMMIT -- fix typo
      .out_2d_unpakced (),
      .cyc (loop_cyc),
      .clk
    );
  end

  intf
  the_intf_a (.*),
  the_intf_b (.*);
  // NOCOMMIT -- intentional decl dupe (pass interface to sub_sub or
  // something)

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

// NOCOMMIT -- change name and don't inline for now?
module some_submodule_we_do_not_want_replicated (
  input a,
  input b,
  output logic x,
  output out_2d_unpakced [3][4],
  input int cyc,
  input clk
);
  /* verilator no_inline_module */
  pkg::some_struct_t the_struct;
  pkg::some_struct_t the_structs [3:0];
  pkg::some_struct_t [2:0] the_packed_structs;
  // NOCOMMIT -- more cases:
  // unpacked struct
  // arrays (packed and unpacked)
  // union
  //
  // NOCOMMIT -- types passed as parameters
  // NOCOMMIT -- test constant structs, etc.
  // NOCOMMIT -- test arrays with different dimensionality for conflicting
  // func names
  // NOCOMMIT -- test typedefed structs
  // NOCOMMIT -- test parameter types which are actually the same

  typedef struct packed {
    logic abc;
    logic def;
    logic xyz;
  } some_struct_t;
  some_struct_t the_local_struct;

  typedef logic [1:0] [31:0] logic_array_t;
  typedef logic [1:0] [31:0] logic_array_2_t;
  logic_array_t the_logic_array;
  logic_array_2_t the_other_logic_array;
  logic [15:0] the_unpacked_array [5];
  logic the_2d_unpakced [3][4];

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
    for (int i = 0; i < 2; i++) begin
      the_logic_array[i] <= cyc + i;
      the_other_logic_array[i] <= cyc + i + 123;
    end
    for (int i = 0; i < 5; i++) the_unpacked_array[i] <= cyc[15:0];
    for (int i = 0; i < 3; i++)
      for (int j = 0; j < 4; j++) begin
        the_2d_unpakced [i][j] <= ~(cyc[i] ^ cyc[j]);
        out_2d_unpakced [i][j] <= cyc[i] ^ cyc[j];
      end
  end
endmodule

interface intf
  (input wire clk);
  logic [3:0] [7:0] data;
  int data_typed;
  always_comb data_typed = data;
endinterface
