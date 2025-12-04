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
      .cyc (loop_cyc),
      .clk
    );
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
endpackage

// NOCOMMIT -- change name and don't inline for now?
module some_submodule_we_do_not_want_replicated (
  input a,
  input b,
  output logic x,
  input int cyc,
  input clk
);
  /* verilator no_inline_module */
  pkg::some_struct_t the_struct;
  // NOCOMMIT -- more cases:
  // unpacked struct
  // arrays (packed and unpacked)
  // union
  //
  // NOCOMMIT -- where is __Vtemp_1 coming from?
  // NOCOMMIT -- deal with full and chg emitted code -> possible it might work
  // but not like we want it to
  // NOCOMMIT -- test colliding type names
  // NOCOMMIT -- test constant structs, etc.

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
  end
endmodule
