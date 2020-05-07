// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   parameter [200:0] TOO_SMALL = 94'd123456789012345678901234567890;  // One to many digits

   parameter [200:0] SMALLH = 8'habc;  // One to many digits
   parameter [200:0] SMALLO = 6'o1234;  // One to many digits
   parameter [200:0] SMALLB = 3'b1111;  // One to many digits

   // We'll allow this though; no reason to be cruel
   parameter [200:0] OKH = 8'h000000001;

   // bug1380
   parameter [128:0] ALSO_SMALL = 129'hdeadbeefc001f00ddeadbeefc001f00ddeadbeefc001f00ddeadbeefc001f00d;

endmodule
