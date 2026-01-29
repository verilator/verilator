// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged union with all void members (maxMemberWidth == 0)
// Covers V3Tagged.cpp line 222

module t;
  typedef union tagged {
    void A;
    void B;
    void C;
  } AllVoid;

  AllVoid av;
  int result;

  initial begin
    av = tagged A;
    result = 0;

    case (av) matches
      tagged A: result = 1;
      tagged B: result = 2;
      tagged C: result = 3;
      default: $stop;
    endcase

    if (result != 1) $stop;

    av = tagged B;
    case (av) matches
      tagged A: result = 1;
      tagged B: result = 2;
      tagged C: result = 3;
      default: $stop;
    endcase

    if (result != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
