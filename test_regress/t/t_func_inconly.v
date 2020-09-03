// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   task main;
      integer varintask;
      varintask = 0;
      while (varintask < 4) begin
         varintask = varintask + 1;
      end
      if (varintask != 4) $stop;
   endtask
   initial begin
      main;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
