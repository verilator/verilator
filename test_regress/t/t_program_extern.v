// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

extern program pgm;

program pgm;
   task ptask;
   endtask
endprogram

module t(/*AUTOARG*/);

   pgm sub ();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
