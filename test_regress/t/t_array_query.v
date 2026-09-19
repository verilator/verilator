// DESCRIPTION: Verilator: System Verilog test of array querying functions.
//
// This code instantiates a module that calls the various array querying
// functions.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Jeremy Bennett, Embecosm
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  wire a = clk;
  wire b = 1'b0;
  reg c;

  array_test array_test_i (  /*AUTOINST*/
      // Inputs
      .clk(clk)
  );

endmodule


// Check the array sizing functions work correctly.
module array_test #(
    parameter LEFT = 5,
    RIGHT = 55
) (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;

  // verilator lint_off ASCRANGE
  reg [7:0] a[LEFT:RIGHT];
  // verilator lint_on ASCRANGE

  typedef reg [7:0] r_t;
  typedef r_t array_t[LEFT:RIGHT];

  task automatic query_dimensions(input int dimension, output int left_bound, right_bound,
                                  array_size);
    // verilator no_inline_task
    left_bound = $left(array_t, dimension);
    right_bound = $right(array_t, dimension);
    array_size = $size(array_t, dimension);
  endtask

  integer l;
  integer r;
  integer s;
  int cycle = 0;

  always @(posedge clk) begin
    l = $left(a);
    r = $right(a);
    s = $size(a);

`ifdef TEST_VERBOSE
    $write("$left (a) = %d, $right (a) = %d, $size (a) = %d\n", l, r, s);
`endif

    if ((l != LEFT) || (r != RIGHT) || (s != (RIGHT - LEFT + 1))) $stop;
    if ($left(r_t) != 7 || $right(r_t) != 0 || $size(r_t) != 8 || $bits(r_t) != 8) $stop;

    // A runtime dimension selects entries in compiler-generated constant tables.
    query_dimensions(cycle[0] ? 2 : 1, l, r, s);
    `checkd(l, cycle[0] ? 7 : LEFT);
    `checkd(r, cycle[0] ? 0 : RIGHT);
    `checkd(s, cycle[0] ? 8 : RIGHT - LEFT + 1);

    cycle <= cycle + 1;
    if (cycle == 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
