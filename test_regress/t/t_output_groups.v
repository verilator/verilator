// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

virtual class Base;
   pure virtual function int get_param;
endclass
class Foo#(int N = 17) extends Base;
   function int get_param;
      return N;
   endfunction
endclass

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   localparam MAX = 128;
   Base q[$];
   generate
      // should result in many C++ files
      genvar i;
      for (i = 0; i < MAX; i++)
         initial begin
            Foo#(i) item = new;
            q.push_back(item);
         end
   endgenerate
   always @(posedge clk) begin
      int sum = 0;
      foreach (q[i])
         sum += q[i].get_param();
      if (sum != MAX * (MAX - 1) / 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
