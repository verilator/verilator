// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk, increment
   );
   input clk;
   input [1:0] increment;

   typedef enum [3:0] {
                       E01 = 1,
                       E03 = 3,
                       E04 = 4,
                       E05 = 5
                       } my_t;

   my_t e;

   always @ (posedge clk) begin
      e.next(increment);
      $finish;
   end

endmodule
