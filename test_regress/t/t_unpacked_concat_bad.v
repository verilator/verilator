// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Driss Hafdi

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   typedef logic [15:0] count_t;
   typedef bit [31:0]   bit_int_t;

   localparam bit_int_t [1:0] count_bits = {2{$bits(count_t)}};

   initial begin
      $write("%d\n", count_bits[0]);
      $write("%d\n", count_bits[1]);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
