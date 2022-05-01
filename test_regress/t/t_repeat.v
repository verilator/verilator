// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   reg signed [2:0] negcnt;
   integer times;
   initial begin
      times = 0;
      repeat (1) begin
         repeat (0) $stop;
         repeat (-1) $stop;
         negcnt = 'sb111;
         // Not all commercial simulators agree on the below stopping or not
         // verilator lint_off WIDTH
         repeat (negcnt) $stop;
         // verilator lint_on  WIDTH
         repeat (5) begin
            repeat (2) begin
               times = times + 1;
            end
         end
      end
      if (times != 10) $stop;
      //
      // verilator lint_off INFINITELOOP
      forever begin
         // verilator lint_on INFINITELOOP
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
