// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   s1 s1 ();
   s2 s2 ();
   s3 s3 ();
   s4 s4 ();
   s5 s5 ();
   s6 s6 ();

   initial begin
      $finish;
   end
endmodule

`begin_keywords "1364-1995"
module s1;
  integer signed; initial signed = 1;
endmodule
`end_keywords

`begin_keywords "1364-2001"
module s2;
  integer bit; initial bit = 1;
endmodule
`end_keywords

`begin_keywords "1364-2005"
module s3;
  integer final; initial final = 1;
endmodule
`end_keywords

`begin_keywords "1800-2005"
module s4;
  integer global; initial global = 1;
endmodule
`end_keywords

`begin_keywords "1800-2009"
module s5;
 final begin
    $write("*-* All Finished *-*\n");
 end
endmodule
`end_keywords

`begin_keywords "VAMS-2.3"
module s6;
   real foo; initial foo = sqrt(2.0);
endmodule
`end_keywords
