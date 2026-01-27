// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2020 engr248
// SPDX-License-Identifier: CC0-1.0

module \foo$bar ;
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
