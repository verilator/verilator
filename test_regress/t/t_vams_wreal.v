// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

`begin_keywords "VAMS-2.3"

module t (/*autoarg*/
   // Outputs
   aout,
   // Inputs
   in
   );

   input [15:0] in;
   output 	aout; 
   wreal aout;

   parameter real lsb = 1;
   // verilator lint_off WIDTH
   assign  aout = $itor(in) * lsb;
   
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
