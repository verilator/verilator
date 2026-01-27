// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Adrien Le Masle
// SPDX-License-Identifier: CC0-1.0

package pack_a;
   parameter PARAM_A = 0;
endpackage : pack_a

//module t;
module t;

   parameter PARAM_A = 0;

   initial begin
      $display(PARAM_A);
      if (PARAM_A != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
