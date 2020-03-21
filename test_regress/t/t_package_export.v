// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

// see bug 591

package pkg1;
   parameter PARAM2 = 16;
   parameter PARAM3 = 16;
endpackage : pkg1


package pkg10;
   import pkg1::*;
   import pkg1::*;  // Ignore if already
`ifdef T_PACKAGE_EXPORT
   export *::*;  // Not supported on all simulators
`endif
   parameter PARAM1 = 8;
endpackage
package pkg11;
   import pkg10::*;
endpackage

package pkg20;
   import pkg1::*;
`ifdef T_PACKAGE_EXPORT
   export pkg1::*;
`endif
   parameter PARAM1 = 8;
endpackage
package pkg21;
   import pkg20::*;
endpackage

package pkg30;
   import pkg1::*;
`ifdef T_PACKAGE_EXPORT
   export pkg1::PARAM2;
   export pkg1::PARAM3;
`endif
   parameter PARAM1 = 8;
endpackage
package pkg31;
   import pkg30::*;
endpackage

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [pkg11::PARAM1 : 0] bus11;
   reg [pkg11::PARAM2 : 0] bus12;
   reg [pkg11::PARAM3 : 0] bus13;

   reg [pkg21::PARAM1 : 0] bus21;
   reg [pkg21::PARAM2 : 0] bus22;
   reg [pkg21::PARAM3 : 0] bus23;

   reg [pkg31::PARAM1 : 0] bus31;
   reg [pkg31::PARAM2 : 0] bus32;
   reg [pkg31::PARAM3 : 0] bus33;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
