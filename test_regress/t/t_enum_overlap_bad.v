// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/);

   enum { e0,
	  e1,
	  e2,
	  e1b=1
	  } BAD1;

   initial begin
      $stop;
   end

endmodule
