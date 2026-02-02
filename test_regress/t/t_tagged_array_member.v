// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged union with array member in pattern matching

module t;
  // Struct with array member
  typedef struct {
    int arr[2];
  } ArrayStruct;

  // Tagged union with struct containing array
  typedef union tagged {
    void Empty;
    ArrayStruct Data;
  } MyUnion;

  MyUnion u;
  int result;

  initial begin
    u = tagged Data '{arr: '{10, 20}};
    result = 0;

    // Pattern matching with array in struct - covers V3Width.cpp lines 5006-5008
    if (u matches tagged Data '{arr: '{.a, .b}}) begin
      result = a + b;
    end

    if (result != 30) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
