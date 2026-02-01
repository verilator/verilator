// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test pattern matching with array-type tagged union member

module t;
  typedef union tagged {
    void Invalid;
    int Numbers[4];  // Array type, NOT struct
  } MyUnion;

  MyUnion u;
  int result;

  initial begin
    u = tagged Numbers '{1, 2, 3, 4};
    result = 0;

    // Pattern for array-type member triggers line 5009
    if (u matches tagged Numbers '{.a, .b, .c, .d}) begin
      result = a + b + c + d;
    end

    if (result != 10) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
