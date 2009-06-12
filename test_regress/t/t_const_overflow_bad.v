// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005-2007 by Wilson Snyder.

module t (/*AUTOARG*/);

   parameter [200:0] TOO_SMALL = 94'd123456789012345678901234567890;  // One to many digits

   parameter [200:0] SMALLH = 8'habc;  // One to many digits
   parameter [200:0] SMALLO = 6'o1234;  // One to many digits
   parameter [200:0] SMALLB = 3'b1111;  // One to many digits
   
   // We'll allow this though; no reason to be cruel
   parameter [200:0] OKH = 8'h000000001;

endmodule
