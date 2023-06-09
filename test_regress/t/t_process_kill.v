// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   process p;
   bit s = 0;

   initial begin
      wait (s);
      p.kill();
      p.await();
      $write("*-* All Finished *-*\n");
      $finish;
   end

   always @(posedge clk) begin
      if (!p) begin
         p = process::self();
         s = 1;
      end else begin
         $stop;
      end
   end
endmodule
