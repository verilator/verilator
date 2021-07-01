// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire  o0, o1;

   sub #(1) a(.i(1'b0), .o(o0));
   sub #(2) b(.i(1'b0), .o(o1));

   always @(posedge clk) begin
      if (o0 != 1'b0) begin
         $write("Bad o0\n");
         $stop;
      end
      if (o1 != 1'b1) begin
         $write("Bad o1\n");
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module sub
  #(
    parameter int W
    )
   (
    input wire  i,
    output wire o
    );

   typedef struct packed {
      logic [W-1:0] a;
   } s;

   sub2 #(s) c(.i(i), .o(o));

endmodule

module sub2
  # (
     parameter type T = logic
     )
   (
    input wire  i,
    output wire o
    );

   if ($bits(T) % 2 == 1) begin
      assign o =  i;
   end else begin
      assign o =  ~i;
   end

endmodule
