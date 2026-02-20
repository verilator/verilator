// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
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

   property check(int n);
      disable iff (n == 0)
        check(n - 1);
   endproperty

   assert property(@(posedge clk) check(1))
     else begin
        // Assertion should pass
        $write("*-* Assertion failed *-*\n");
        $stop;
     end

   always @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
