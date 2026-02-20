// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   initial begin
      $display("""First "quoted"\nsecond\
third
fourth""");

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
