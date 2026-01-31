// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged pattern without value binding (tagged Member without .var)
// Covers V3Tagged.cpp lines 268 (right branch) and 659

module t;
  typedef union tagged { void Invalid; int Valid; } VInt;
  VInt v;
  int result;

  initial begin
    v = tagged Valid (42);
    result = 0;

    // Case matches with non-void member but no binding
    // This creates AstTaggedExpr in pattern position (grammar line 5060)
    case (v) matches
      tagged Invalid: result = -1;
      tagged Valid: result = 1;  // Non-void member, no binding
      default: $stop;
    endcase

    if (result != 1) $stop;

    // Also test void member case
    v = tagged Invalid;
    case (v) matches
      tagged Invalid: result = 2;
      tagged Valid: result = -1;
      default: $stop;
    endcase

    if (result != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
