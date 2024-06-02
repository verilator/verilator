// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

//
// Constants should not be shared by different non-inlined modules
//

module a(
         input wire clk,
         input wire trig_i,
         output reg trig_o
         );
   /* verilator no_inline_module */

   // Same constant as in module b
   wire [255:0]     C = {32'h1111_1111,
                         32'h2222_2222,
                         32'h3333_3333,
                         32'h4444_4444,
                         32'h5555_5555,
                         32'h6666_6666,
                         32'h7777_7777,
                         32'h8888_8888};

   int i;

   always @(posedge clk) begin
      trig_o <= 1'd0;
      if (trig_i) begin
         // Note: Base index via $c to prevent optimizatoin by Verilator
         i = $c(0*32); $display("0x%8x", C[i+:32]);
         i = $c(2*32); $display("0x%8x", C[i+:32]);
         i = $c(4*32); $display("0x%8x", C[i+:32]);
         i = $c(6*32); $display("0x%8x", C[i+:32]);
         $display("0x%32x", C);
         trig_o <= 1'd1;
      end
   end

endmodule

module b(
         input wire clk,
         input wire trig_i,
         output reg trig_o
         );
   /* verilator no_inline_module */

   // Same constant as in module a
   wire [255:0]     C = {32'h1111_1111,
                         32'h2222_2222,
                         32'h3333_3333,
                         32'h4444_4444,
                         32'h5555_5555,
                         32'h6666_6666,
                         32'h7777_7777,
                         32'h8888_8888};

   int i;

   always @(posedge clk) begin
      trig_o <= 1'd0;
      if (trig_i) begin
         // Note: Base index via $c to prevent optimizatoin by Verilator
         i = $c(1*32); $display("0x%8x", C[i+:32]);
         i = $c(3*32); $display("0x%8x", C[i+:32]);
         i = $c(5*32); $display("0x%8x", C[i+:32]);
         i = $c(7*32); $display("0x%8x", C[i+:32]);
         $display("0x%32x", C);
         trig_o <= 1'd1;
      end
   end

endmodule

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc = 0;

   reg     trig_i;
   wire    trig_ab;
   wire    trig_o;

   a a_inst(.clk(clk), .trig_i(trig_i), .trig_o(trig_ab));
   b b_inst(.clk(clk), .trig_i(trig_ab), .trig_o(trig_o));

   always @(posedge clk) begin
      trig_i <= cyc == 1;

      if (trig_o) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end

      cyc++;
   end

endmodule
