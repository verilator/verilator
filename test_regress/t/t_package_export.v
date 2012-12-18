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
`ifdef T_PACKAGE_EXPORT
   export pkg2::*;  // Not supported on all simulators
`endif
   parameter PARAM1 = 8;
endpackage // pkg1

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   import pkg1::*;

   reg [PARAM1:0] bus1;
   reg [PARAM2:0] bus2;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
