// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

//`begin_keywords "VAMS-2.3"
`begin_keywords "1800+VAMS"

module t (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in
   );

   input in;
   wreal in;
   output out; 
   wreal out; 

   import "DPI-C" context function void dpii_call(input real in, output real out);

   initial begin 
      dpii_call(in,out);
      $finish;
   end

endmodule
