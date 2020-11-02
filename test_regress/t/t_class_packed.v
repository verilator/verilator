// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   //TODO sub #(.WIDTH(1)) w1;
   //TODO sub #(.WIDTH(2)) w2;
   //TODO sub #(.WIDTH(3)) w3;
   //TODO sub #(.WIDTH(4)) w4;
   sub #(.WIDTH(5)) w5;

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub ();
   parameter WIDTH=5; // WIDTH >= 5 fails. WIDTH <= 4 passes

   typedef struct packed {
      logic [WIDTH-1:0] data;
      } [15:0] w_t;

   class WrReqQ;
      w_t w;
   endclass

   initial begin
      if ($bits(w_t) != WIDTH * 16) $stop;
   end

endmodule
