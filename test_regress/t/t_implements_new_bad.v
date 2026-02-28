// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface class Icls;
endclass

module t;
   Icls c;
   initial begin
      c = new;  // Bad
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
