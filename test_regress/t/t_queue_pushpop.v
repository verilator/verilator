// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic q [$];
   int   cycle = 0;

   always @(posedge clk) begin
      cycle <= cycle + 1'b1;
   end

   always @(posedge clk) begin
      q.push_front(1'b1);
   end

   // Important this is a separate always to expose bug where "q" thought unused
   always @(posedge clk) begin
      if (cycle == 1) begin
         if (q.pop_back() != 1) $stop;
      end
   end

   always @(posedge clk) begin
      if (cycle == 2) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
