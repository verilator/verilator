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
      check(cyc_mod_2, 1);
   endproperty

   property check_if_gt_5(int cyc);
      @(posedge clk)
        cyc > 5;
   endproperty

   property pass_assertion(int cyc);
      disable iff (cyc <= 10)
      cyc > 10;
   endproperty

   int expected_fails = 0;

   assert property(check(0, 1))
     else begin
        // Assertion should pass
        $display("Assert failed, but shouldn't");
        $stop;
     end
   assert property(check(1, 1))
     else begin
        // Assertion should fail
        expected_fails += 1;
     end
   assert property(check_if_1(1))
     else begin
        // Assertion should fail
        expected_fails += 1;
     end
   assert property(disable iff (cyc < 5) check_if_gt_5(cyc + 1));
   assert property(@(posedge clk) pass_assertion(cyc));

   always @(posedge clk) begin
      if (expected_fails == 2) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
