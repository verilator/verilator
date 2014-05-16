// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett

// see bug 591

package pkg2;
   parameter PARAM2 = 16;
endpackage // pkg2

package pkg1;
   import pkg2::*;
   parameter PARAM1 = 8;
endpackage // pkg1

module t
  import pkg1::*;   // Test SV 2012 import format
  (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [PARAM1:0] bus1;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
