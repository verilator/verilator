// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
      clk
   );

   input clk;
   int cyc = 0;
   logic [4:0] val = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      val = ~val;
   end

   property check(cyc_mod_2, logic [4:0] expected, arg3, untyped arg4, arg5);
      @(posedge clk)
        cyc % 2 == cyc_mod_2 |=> val == expected;
   endproperty

   assert property(check(0, 5'b11111, 100, 25, 17));

   always @(posedge clk) begin
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
