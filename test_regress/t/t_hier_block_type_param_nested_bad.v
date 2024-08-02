// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t(
   clk
   );
   input clk;
   logic [2:0] in1;
   logic [2:0] out1;

   assign in1 = 0;

   Test #(.TYPE_t(logic[2:0])) test(.out (out1), .in (in1));

   logic [3:0] in2;
   logic [3:0] out2;

   assign in2 = 0;
   Test #(.TYPE_t(logic[3:0])) test2(.out (out2), .in (in2));

   always @ (posedge clk) begin
      if (out1 !== ~in1) $stop;
      if (out2 !== ~in2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module Test
   #(parameter type TYPE_t = logic [5:0])
   (
   output TYPE_t out,
   input TYPE_t in
   ); /*verilator hier_block*/

   SubTest #(.TYPE_t(TYPE_t)) subTest(.out(out), .in(in));
endmodule

module SubTest
   #(parameter type TYPE_t = logic [8:0])
   (
   output TYPE_t out,
   input TYPE_t in
   ); /*verilator hier_block*/

   assign out = ~ in;
endmodule
