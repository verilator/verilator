// DESCRIPTION: Verilator: Verilog Test module
//
// The value of a force on an unpacked aggregate is kept in a shadow variable
// typed as the target, so the right-hand side must be of the target's type.
// An expression of another type is diagnosed rather than mis-stored.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef struct {
    logic [7:0] x;
    logic [7:0] y;
  } inner_t;
  typedef struct {
    inner_t sub;
    logic [7:0] pad;
  } outer_t;
  // A single-member unpacked struct is a typed-shadow target too, though its slot
  // count is one, so a differently-typed right-hand side is diagnosed the same way
  typedef struct {
    logic [7:0] only;
  } one_t;
  outer_t s;
  one_t one;
  initial begin
    force s = '0;
    force s.sub = '0;
    force one = '0;
    $finish;
  end
endmodule
