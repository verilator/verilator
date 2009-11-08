// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

typedef int unit_type_t;

function [3:0] unit_plusone(input [3:0] i);
   unit_plusone = i+1;
endfunction

package p;
   typedef int package_type_t;
   function [3:0] plusone(input [3:0] i);
      plusone = i+1;
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

   initial begin
      if (unit_plusone(1) !== 2) $stop;
      if ($unit::unit_plusone(1) !== 2) $stop;
      if (p::plusone(1) !== 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
