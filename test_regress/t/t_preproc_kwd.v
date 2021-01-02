// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   v95 v95 ();
   v01nc v01nc ();
   v01c v01c ();
   v05 v05 ();
   s05 s05 ();
   s09 s09 ();
   s12 s12 ();
   s17 s17 ();

   a23 a23 ();

   initial begin
      $finish;
   end
endmodule

`begin_keywords "1364-1995"
module v95;
  integer signed; initial signed = 1;
endmodule
`end_keywords

`begin_keywords "1364-2001-noconfig"
module v01nc;
  localparam g = 0;
  integer instance; initial instance = 1;
endmodule
`end_keywords

`begin_keywords "1364-2001"
module v01c;
  localparam g = 0;
  integer bit; initial bit = 1;
endmodule
`end_keywords

`begin_keywords "1364-2005"
module v05;
  uwire w;
  integer final; initial final = 1;
endmodule
`end_keywords

`begin_keywords "1800-2005"
module s05;
  bit b;
  integer global; initial global = 1;
endmodule
`end_keywords

`begin_keywords "1800-2009"
module s09;
   bit b;
   integer soft; initial soft = 1;
endmodule
`end_keywords

`begin_keywords "1800-2012"
module s12;
 final begin
    $write("*-* All Finished *-*\n");
 end
endmodule
`end_keywords

`begin_keywords "1800-2017"
module s17;
 final begin
    $write("*-* All Finished *-*\n");
 end
endmodule
`end_keywords

`begin_keywords "VAMS-2.3"
module a23;
   real foo; initial foo = sqrt(2.0);
endmodule
`end_keywords
