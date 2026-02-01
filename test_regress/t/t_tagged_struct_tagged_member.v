// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test struct pattern with tagged union member

module t;
  typedef union tagged {
    void None;
    int Value;
  } MaybeInt;

  typedef struct {
    int a;
    MaybeInt maybe;  // Tagged union as struct member
  } MyStruct;

  typedef union tagged {
    void Empty;
    MyStruct Data;
  } Outer;

  Outer o;
  int result;

  initial begin
    o = tagged Data '{a: 1, maybe: tagged Value (42)};
    result = 0;

    // '{a: .x, maybe: tagged Value .y} triggers line 5851
    if (o matches tagged Data '{a: .x, maybe: tagged Value .y}) begin
      result = x + y;
    end

    if (result != 43) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
