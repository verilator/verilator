// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/);
  initial begin
    bit q1[$] = {1'b1};
    bit q2[$];
    bit q3[$];
    bit [1:0] d1[] = {2'b10};
    bit [1:0] d2[];
    // TODO: queue streaming support broke assignment like this.
    // It's something to do witih computeCastable and V3Width.cpp
    // q2 = {q1};
    // if (q2[0] != 1) $stop;

    q3 = q1;
    if (q3[0] != 1) $stop;

    d2 = {2'b11};
    if (d2[0] != 2'b11) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
