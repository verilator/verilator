// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`ifdef verilator
 `define dontOptimize $c1("1")
`else
 `define dontOptimize 1'b1
`endif

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc = 0;
   int x = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      x = 32'hcafe1234;

      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
      if (`dontOptimize) if (`dontOptimize) if (`dontOptimize) if (`dontOptimize)
          x = cyc;

      $write("[%0t] cyc=%0d x=%x\n", $time, cyc, x);
      if (x !== cyc) $stop;
      if (cyc == 99) begin
          $write("*-* All Finished *-*\n");
          $finish;
      end
   end
endmodule
