// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;

  initial begin
    bit q1[$] = {1'b1};
    bit q2[$];
    bit q3[$];

    bit [1:0] d1[$] = {2'b10};
    bit [1:0] d2[$];
    bit [1:0] d3[$];

    q2 = {q1};  // consCC
    if (q2.size != 1) $stop;
    if (q2[0] != 1) $stop;

    q3 = q1;
    if (q3.size != 1) $stop;
    if (q3[0] != 1) $stop;

    if (d1[0] != 2'b10) $stop;

    d2 = {2'b11};
    if (d2[0] != 2'b11) $stop;

    d3 = {d1, d2};
    if (d3[0] != 2'b10) $stop;
    if (d3[1] != 2'b11) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
