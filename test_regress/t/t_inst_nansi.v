// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(b, si, i, li, w3, w4);
  output b;  // Output before type
  output si;
  byte b;
  shortint si;

  int i;
  longint li;
  output i;  // Output after type
  output li;

  input w3;
  wire [2:0] w3;
  wire [3:0] w4;
  input w4;

  initial begin
    if ($bits(b) != 8) $stop;
    if ($bits(si) != 16) $stop;
    if ($bits(i) != 32) $stop;
    if ($bits(li) != 64) $stop;
    if ($bits(w3) != 3) $stop;
    if ($bits(w4) != 4) $stop;
    $finish;
  end

endmodule
