// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   function void allfin;
      $write("*-* All Finished *-*\n");
   endfunction

   task done;
      $finish;
   endtask

   initial begin
      allfin();
      done();
   end
endmodule
