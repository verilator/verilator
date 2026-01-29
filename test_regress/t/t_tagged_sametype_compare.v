// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test comparing different tagged union types
// Covers V3AstNodes.cpp sameNode() branches for tagBitWidth and maxMemberWidth

module t;
  // Two different tagged unions with different tag widths and member widths
  typedef union tagged {
    void Invalid;
    int Valid;
  } TwoMember;  // tagBitWidth=1, maxMemberWidth=32

  typedef union tagged {
    void A;
    void B;
    void C;
    void D;
    int E;
  } FiveMember;  // tagBitWidth=3, maxMemberWidth=32

  typedef union tagged {
    void Small;
    bit [7:0] Byte;
  } SmallMember;  // tagBitWidth=1, maxMemberWidth=8

  TwoMember t2;
  FiveMember f5;
  SmallMember sm;

  initial begin
    t2 = tagged Valid (42);
    f5 = tagged E (42);
    sm = tagged Byte (8'hAB);

    // Test that each type works independently
    if (t2 matches tagged Valid .v) begin
      if (v != 42) $stop;
    end else $stop;

    if (f5 matches tagged E .v) begin
      if (v != 42) $stop;
    end else $stop;

    if (sm matches tagged Byte .b) begin
      if (b != 8'hAB) $stop;
    end else $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
