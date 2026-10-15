// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
  string s[] = {"hello", "sad", "sad", "world"};

  initial begin
    bit b;

    b = s.unknown_bad;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
