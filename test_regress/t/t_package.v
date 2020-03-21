// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef int unit_type_t;

function [3:0] unit_plusone(input [3:0] i);
   unit_plusone = i+1;
endfunction

package p;
   typedef int package_type_t;
   integer     pi = 123;
   function [3:0] plusone(input [3:0] i);
      plusone = i+1;
   endfunction
endpackage

package p2;
   typedef int package2_type_t;
   function [3:0] plustwo(input [3:0] i);
      plustwo = i+2;
   endfunction
endpackage

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   unit_type_t vu;
   $unit::unit_type_t vdu;
   p::package_type_t vp;

   t2 t2 ();

   initial begin
      if (unit_plusone(1) !== 2) $stop;
      if ($unit::unit_plusone(1) !== 2) $stop;
      if (p::plusone(1) !== 2) $stop;
      p::pi = 124;
      if (p::pi !== 124) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
   always @ (posedge clk) begin
      p::pi += 1;
      if (p::pi < 124) $stop;
   end
endmodule

module t2;
   import p::*;
   import p2::plustwo;
   import p2::package2_type_t;
   package_type_t vp;
   package2_type_t vp2;
   initial begin
      if (plusone(1) !== 2) $stop;
      if (plustwo(1) !== 3) $stop;
      if (p::pi !== 123 && p::pi !== 124) $stop;  // may race with other initial, so either value
   end
endmodule
