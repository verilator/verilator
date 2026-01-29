// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged union with single member (tagBitWidth == 0)
// Covers V3Tagged.cpp line 248

module t;
  typedef union tagged {
    int Only;
  } SingleMember;

  SingleMember sm;
  int result;

  initial begin
    sm = tagged Only (42);
    result = 0;

    if (sm matches tagged Only .n) result = n;

    if (result != 42) $stop;

    sm = tagged Only (123);
    case (sm) matches
      tagged Only .n: result = n;
      default: $stop;
    endcase

    if (result != 123) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
