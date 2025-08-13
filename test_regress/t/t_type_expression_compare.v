// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

typedef int Int_T;

module t;
   initial begin
      Int_T value1 = 7;
      int value2 = 13;
      if (type(value1) != type(value2)) $stop;
      if (type(value1 + value2) != type(value2 + 18)) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
