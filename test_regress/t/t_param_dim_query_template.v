// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// A module instantiated both with and without parameter overrides is used
// directly for the non-overriding instance, while also being the template the
// specialized clone is made from.  Dimension queries of a type declared in that
// module must still fold to a constant there, as a parameter value may depend
// on it, and each instance must see its own parameters.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub #(
    parameter int W = 1,
    parameter int E = 0
) ();
  initial `checkd(W, E);
endmodule

module mid #(
    parameter int P = 3
) ();
  typedef logic [2*P:P] data_t;
  localparam int BITS = $bits(data_t);
  sub #(
      .W(BITS),
      .E(P + 1)
  ) i_bits ();
  localparam int HIGH = $high(data_t);
  sub #(
      .W(HIGH),
      .E(2 * P)
  ) i_high ();
  localparam int LOW = $low(data_t);
  sub #(
      .W(LOW),
      .E(P)
  ) i_low ();
  localparam int SIZE = $size(data_t);
  sub #(
      .W(SIZE),
      .E(P + 1)
  ) i_size ();
  localparam int INCREMENT = $increment(data_t);
  sub #(
      .W(INCREMENT),
      .E(1)
  ) i_increment ();
  localparam int LEFT = $left(data_t);
  sub #(
      .W(LEFT),
      .E(2 * P)
  ) i_left ();
  localparam int RIGHT = $right(data_t);
  sub #(
      .W(RIGHT),
      .E(P)
  ) i_right ();

  typedef logic [P:2*P] asc_t;
  localparam int INCREMENT_ASC = $increment(asc_t);
  sub #(
      .W(INCREMENT_ASC),
      .E(-1)
  ) i_increment_asc ();
  localparam int LEFT_ASC = $left(asc_t);
  sub #(
      .W(LEFT_ASC),
      .E(P)
  ) i_left_asc ();
  localparam int RIGHT_ASC = $right(asc_t);
  sub #(
      .W(RIGHT_ASC),
      .E(2 * P)
  ) i_right_asc ();
endmodule

module t ();
  // No overrides, so this instance uses the template module itself
  mid i_default ();
  // Overrides, so this instance makes the module above a template
  mid #(.P(5)) i_override ();
  // Override equal to the default
  mid #(.P(3)) i_same ();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
