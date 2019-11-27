// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

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
