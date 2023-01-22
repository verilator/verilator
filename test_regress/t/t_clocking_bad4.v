// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic in, out;
   clocking cb1 @(posedge clk);
       input in;
       output out;
   endclocking

   int cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   clocking cb2 @(negedge clk);
       input #cyc in;
       input #(-1) out;
   endclocking

   task write(output x);
       x = 1;
   endtask

   always ##1;
   always cb1.out = clk;
   assign cb1.out = clk;
   always write(cb1.out);
   always cb1.out <= @(posedge clk) 1;
   always cb1.out <= #1 1;
   always out <= ##1 1;

   always @(posedge clk) begin
       cb1.in = 1;
       $display(cb1.out);
   end
endmodule
