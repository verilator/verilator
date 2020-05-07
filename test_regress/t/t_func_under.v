// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [3:0] counter = 0;
   integer   l2;
   function log2 (input [3:0] x);
      integer log2 = (x < 2) ? 1 : (x < 4) ? 2 : (x < 8) ? 3 : 4;
   endfunction
   always @(posedge clk) begin
      counter <= counter + 1;
      l2 <= log2(counter);
      // bug589: This failed with (%Error: Internal Error: Function not underneath a statement):
      $display("log2(%d) == %d", counter, log2(counter));
      //
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
