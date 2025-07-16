// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module tb2 ();
   parameter CLK_PERIOD = 2;

   reg clk = 1'b0;
   int messages;

   always #(CLK_PERIOD / 2) clk = ~clk;

   always begin
      int counter = 0;
      while (counter < 3) begin
         counter += 1;
         $display("[%0t] Running loop %0d", $time, counter);
         messages += 1;
         @(posedge clk);
      end

      $write("[%0t] *-* All Finished *-*\n", $time);
      $finish;
   end

   final `checkd(messages, 3);

endmodule
