// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   initial begin
      // verilator lint_off FUTURE1
      $write("*-* All Finished *-*\n");
      $finish;
      // verilator FUTURE2
      // verilator FUTURE2 blah blah
   end
endmodule
