// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t #
  (
   parameter   PIPE = 4
   )(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // These are ok
   sub #(
         .P_STOP     (1)
         ) u_sub1 ();
   sub #(
         .P_STOP     (0)
         ) u_sub0 ();

   genvar         i;
   for (i = -1; i < 1; i++) begin: SUB_PIPE
      sub #(
            .P_STOP     (i)
            ) u_sub ();
   end

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module sub #
  (
   parameter P_START = 1,
   parameter P_STOP  = 0
   )(
     );

   initial begin
      for (int i = P_START; i >= P_STOP; --i) begin
         $display("%m %0d..%0d i=%0d", P_START, P_STOP, i);
      end
   end

endmodule
