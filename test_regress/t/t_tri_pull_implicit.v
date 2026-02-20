// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   // verilator lint_off IMPLICIT
   pulldown (pd);
   pullup (pu);

   initial begin
      if (pd != 0) $stop;
      if (pu != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
