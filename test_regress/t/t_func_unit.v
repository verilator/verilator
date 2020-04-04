// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

task tsk(output tfo);
   tfo = 1'b0;
endtask

module t (/*AUTOARG*/
   // Outputs
   to
   );
   output reg to[2:0];

   integer i = 0;

   initial begin
      tsk(to[i]);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
