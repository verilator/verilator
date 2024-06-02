// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   module_with_assert module_with_assert(clk);
   module_with_assertctl module_with_assertctl(clk);

   always @ (posedge clk) begin
      assert(0);
   end

   always @ (negedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module module_with_assert(input clk);
    always @(posedge clk) assert(0);
endmodule

module module_with_assertctl(input clk);
   let ON = 3;
   let OFF = 4;
   let KILL = 5;

   function void assert_off; begin
      $assertoff;
   end
   endfunction
   function void assert_on; begin
      $asserton;
   end
   endfunction
   function void f_assert; begin
      assert(0);
   end
   endfunction

   initial begin
      assert(0);
      $assertoff;
      assert(0);
      $asserton;
      assert(0);
      $assertkill;
      assert(0);

      $assertcontrol(ON);
      assert(0);
      $assertcontrol(OFF);
      assert(0);
      $assertcontrol(ON);
      assert(0);
      $assertcontrol(KILL);
      assert(0);

      assert_on();
      assert(0);
      assert_off();
      assert_off();
      assert(0);
      assert_on();
      assert_on();
      assert(0);

      f_assert();
      f_assert();
      assert_off();
      f_assert();
      f_assert();
   end
endmodule
