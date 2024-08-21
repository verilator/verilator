// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t(
   clk
   );
   input clk;
   logic [31:0] in1;
   logic [31:0] out1;

   assign in1 = 0;

   Test #(.TYPE_t(logic[31:0])) test(.out (out1), .in (in1));

   always @ (posedge clk) begin
      if (out1 !== ~in1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module Test
   #(parameter type TYPE_t = logic [4:0])
   (
   output TYPE_t out,
   input TYPE_t in
   );
   /*verilator hier_block*/

   assign out = ~ in;
endmodule
