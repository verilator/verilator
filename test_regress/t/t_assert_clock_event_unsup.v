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
        cyc % 2 == cyc_mod_2 |=> val == expected;
   endproperty

   property check_if_1(int cyc_mod_2);
      @(negedge clk)
        check(cyc_mod_2, 1);
   endproperty

   assert property(check_if_1(1))
     else begin
        // Assertion should fail
        $write("*-* All Finished *-*\n");
        $finish;
     end

endmodule
