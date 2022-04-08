// DESCRIPTION: Verilator: Verilog Test module for Issue#2863
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Julien Margetts (Originally provided by Thomas Sailer)

module test
  (input  logic [1:0] a,
   input  logic       e,
   output logic [1:0] z);

   always_latch
     if (e)
       z[0] <= a[0];

   always_latch
     if (e)
       z[1] <= a[1];

endmodule
