// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic clk = 0;
   initial forever #5 clk = ~clk;
   int cyc = 0;
   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 4) begin
         $write("*-* All Finished *-*\n");
         $finish();
      end
   end

   // Skew 0
   logic ok1 = 1;
   always @(posedge clk)
      if (cyc == 0) begin
         if (!ok1) $stop;
         #1 cb.ok1 <= 0;
         #1 if (!ok1) $stop;
      end else if (cyc == 1) begin
         if (!ok1) $stop;
         #1 if (ok1) $stop;
      end
      else if (cyc == 2) ok1 <= 1;
      else if (!ok1) $stop;

   // Skew > 0
   logic ok2 = 1;
   always @(posedge clk)
      if (cyc == 0) begin
         if (!ok2) $stop;
         #1 cb.ok2 <= 0;
         #2 if (!ok2) $stop;
         #3 if (!ok2) $stop;
      end else if (cyc == 1) begin
         if (!ok2) $stop;
         #1 if (!ok2) $stop;
         #2 if (ok2) $stop;
      end
      else if (cyc == 2) ok2 <= 1;
      else if (!ok2) $stop;

   // No timing
   logic ok3 = 0;
   always @(posedge clk)
      if (cyc == 0) ok3 <= 1;
      else if (cyc == 1) if (!ok3) $stop;

   // Clocking (used in all tests)
   clocking cb @(posedge clk);
      output ok1;
      output #1 ok2;
      output ok3;
   endclocking
endmodule
