// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   initial
      fork
         begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      join_none
endmodule
