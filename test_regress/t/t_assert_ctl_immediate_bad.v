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

   clk_module_with_assert clk_module_with_assert(.clk(clk));
   clk_module_with_assert_and_assertctl clk_module_with_assert_and_assertctl(.clk(clk));
   module_with_assert module_with_assert();
   empty_module_with_child_assert empty_module_with_child_assert();
   multiple_asserts multiple_asserts();
   multiple_assertctls multiple_assertctls();

   nested_clk_module_with_assert_and_assertctl nested_clk_module_with_assert_and_assertctl(.clk(clk));
   nested_multiple_asserts nested_multiple_asserts();
   nested_multiple_assert_instances nested_multiple_assert_instances();
   nested_multiple_assertctl_instances nested_multiple_assertctl_instances();
   nested_module_with_assert nested_module_with_assert();
   nested_module_with_assertctl nested_module_with_assertctl();
   nested_multiple_assertctls nested_multiple_assertctls();

   recursive recursive();

   assert_function assert_function();

   assertcontrol assertcontrol();

   always @ (negedge clk) begin
      assert(0);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module clk_module_with_assert_and_assertctl(input clk);
   always @ (posedge clk) begin
      $assertoff;
      assert(0);
   end
endmodule

module nested_clk_module_with_assert_and_assertctl(input clk);
   clk_module_with_assert clk_module_with_assert(.clk(clk));
   always @ (posedge clk) begin
      $assertoff;
      assert(0);
   end
endmodule

module clk_module_with_assert(input clk);
   always @(posedge clk) begin
      assert(0);
   end
endmodule

module nested_multiple_asserts;
   multiple_asserts multiple_asserts();
   initial begin
      $assertoff;
      assert(0);
      assert(0);
      assert(0);
   end
endmodule

module multiple_asserts;
   initial begin
      assert(0);
      assert(0);
      assert(0);
   end
endmodule

module nested_multiple_assertctls;
   multiple_assertctls multiple_assertctls();
   initial begin
      $assertoff;
      $assertoff;
      assert(0);
      $assertoff;
      $assertoff;
   end
endmodule

module multiple_assertctls;
   initial begin
      $assertoff;
      $assertoff;
      assert(0);
      $assertoff;
      $assertoff;
   end
endmodule

module empty_module_with_child_assert;
   module_with_assert module_with_assert();
endmodule

module module_with_assert;
   initial begin
      assert(0);
   end
endmodule

module nested_module_with_assertctl;
   module_with_assertctl module_with_assertctl();
endmodule

module module_with_assertctl;
   initial begin
      $assertoff;
   end
endmodule

module nested_module_with_assert;
   module_with_assert module_with_assert();
   initial begin
      $assertoff;
   end
endmodule

module nested_multiple_assert_instances;
   module_with_assert module_with_assert1();
   module_with_assert module_with_assert2();
   module_with_assert module_with_assert3();
   initial begin
      $assertoff;
   end
endmodule

module nested_multiple_assertctl_instances;
   module_with_assertctl module_with_assertctl1();
   module_with_assertctl module_with_assertctl2();
   module_with_assertctl module_with_assertctl3();
   initial begin
      assert(0);
   end
endmodule

module recursive #(parameter N = 5);
   generate if (N == 5) begin
      recursive #(.N(N - 1)) recursive();
      initial begin
         $assertoff;
      end
   end else if (N > 0) begin
      recursive #(.N(N - 1)) recursive();
      initial begin
         assert(0);
      end
   end
   else begin
      initial begin
         assert(0);
      end
   end endgenerate
endmodule

module assert_function;
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

   module_with_assert module_with_assert();

   initial begin
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

module assertcontrol;
   initial begin
      $assertcontrol(3); // $asserton
      assert(0);
      $assertcontrol(4); // $assertoff
      assert(0);
      $assertcontrol(3); // $asserton
      assert(0);
      $assertcontrol(5); // $assertkill
      assert(0);
   end
endmodule
