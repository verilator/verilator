// DESCRIPTION: Verilator: Demonstrate struct literal param assignment problem
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module sub #(parameter int param_a, parameter bit [1:0] enum_param = '0) ();
   typedef enum logic [1:0] {
       FOO = enum_param,
       BAR,
       BAZ
   } enum_t;
   enum_t the_enum = enum_t'(1);

   initial $display("%s", the_enum.name());
endmodule

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // finish report
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   sub #(.param_a(1)) the_sub1();
   sub #(.param_a(2)) the_sub2();
   sub #(.param_a(2), .enum_param(2'd1)) the_sub3();

endmodule
