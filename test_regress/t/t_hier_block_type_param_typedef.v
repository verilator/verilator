// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t(
   clk
   );
   input clk;
   logic [21:0] in1;
   logic [21:0] out1;

   assign in1 = 0;
   typedef logic[21:0] PARAM_T;
   Test #(.TYPE_t(PARAM_T)) test(.out (out1), .in (in1));

   logic [63:0] in2;
   logic [63:0] out2;

   assign in2 = 0;
   typedef logic[63:0] PARAM2_T;
   Test #(.TYPE_t(PARAM2_T)) test2(.out (out2), .in (in2));

   always @ (posedge clk) begin
      if (out1 !== ~in1) $stop;
      if (out2 !== ~in2) $stop;
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
