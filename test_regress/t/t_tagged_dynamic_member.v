// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged unions with dynamic/string members
// This exercises the V3EmitCHeaders code path for dynamic types

module t;
  typedef union tagged {
    void Empty;
    string Msg;
  } Dynamic;

  Dynamic d;
  string result;

  initial begin
    d = tagged Empty;

    d = tagged Msg ("Hello");
    if (d matches tagged Msg .s) result = s;
    if (result != "Hello") $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
