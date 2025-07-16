// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int   cyc;
   bit   valid;

   property prop;
      int prevcyc;
      (valid, prevcyc = cyc) |=> (cyc == prevcyc + 1);
   endproperty

   default clocking @(posedge clk); endclocking
   assert property(prop);

   property with_def(int nine = 9);
      cyc == 9 |-> cyc == nine;
   endproperty

   assert property(with_def);

   always @(posedge clk) begin
      cyc <= cyc + 1;
      valid <= cyc == 5;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
