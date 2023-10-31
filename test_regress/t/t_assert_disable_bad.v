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
   logic val = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      val = ~val;
   end

   property check(int cyc_mod_2, logic expected);
      @(posedge clk)
        disable iff (cyc == 0) cyc % 2 == cyc_mod_2 |=> val == expected;
   endproperty

   // Test should fail due to duplicated disable iff statements
   // (IEEE 1800-2012 16.12.1).
   assert property (disable iff (val == 0) check(1, 1));
endmodule
