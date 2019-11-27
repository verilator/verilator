// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

module t (/*AUTOARG*/);

   string s;
   integer i;

   // Check constification
   initial begin
      s="1234";
      i = s.len(0); // BAD
      s.itoa;  // BAD
      s.itoa(1,2,3);  // BAD
   end

endmodule
