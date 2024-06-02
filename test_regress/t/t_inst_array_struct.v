// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   typedef struct packed {
      bit         one;
      bit         two;
   } ps_t;

   ps_t in0 [2];
   ps_t out0 [2];

   bit [1:0] in1 [2] = {{1'b1, 1'b0}, {1'b0, 1'b1}};
   bit [1:0] out1 [2];

   Sub sub0 [2] (in0, out0);
   Sub sub1 [2] (in1, out1);

   int       cyc;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      in0 = {{1'b1, 1'b0}, {1'b0, 1'b1}};
      if (cyc == 9) begin
         $display("%p %p", in0, out0);
         $display("%p %p", in1, out1);
         if (out0[0] != 2'h2 || out0[1] != 2'h1) $stop;
         if (out1[0] != 2'h2 || out1[1] != 2'h1) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Sub
  (input bit [1:0] in,
   output bit [1:0] out);
   assign out = in;
endmodule
