// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t();
   std::process proc;
   logic clk = 0;
   logic b = 0;

   always #1 clk = ~clk;

   task kill_me_after_1ns();
      fork
         #1 proc.kill();
         #3 begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      join_none
   endtask

   always @(posedge clk) begin
      if (!b) begin
         proc = std::process::self();
         kill_me_after_1ns();
         b = 1;
      end else begin
         $stop;
      end
   end
endmodule
