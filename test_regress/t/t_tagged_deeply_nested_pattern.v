// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test deeply nested struct patterns in tagged union

module t;
  typedef struct {
    int x;
    int y;
  } Inner;

  typedef struct {
    int a;
    Inner inner;  // Nested struct
  } Outer;

  typedef union tagged {
    void Empty;
    Outer Data;
  } MyUnion;

  MyUnion u;
  int result;

  initial begin
    u = tagged Data '{a: 1, inner: '{x: 2, y: 3}};
    result = 0;

    // Nested struct pattern '{x: .x_val, y: .y_val} triggers lines 5855-5856
    if (u matches tagged Data '{a: .a_val, inner: '{x: .x_val, y: .y_val}}) begin
      result = a_val + x_val + y_val;
    end

    if (result != 6) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
