// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

`begin_keywords "1364-1995"
  integer signed; initial signed = 1;
`end_keywords
`begin_keywords "1364-2001"
  integer bit; initial bit = 1;
`end_keywords
`begin_keywords "1364-2005"
  integer final; initial final = 1;
`end_keywords
`begin_keywords "1800-2005"
  integer global; initial global = 1;
 `begin_keywords "1800-2009"
  final begin
     $write("*-* All Finished *-*\n");
  end
 `end_keywords
`end_keywords

   initial begin
      $finish;
   end
endmodule
