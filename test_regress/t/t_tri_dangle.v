// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inouts
   AVDD, AVSS
   );
   inout AVDD;
   inout  AVSS;

   sub sub (/*AUTOINST*/
	    // Inouts
	    .AVDD			(AVDD),
	    .AVSS			(AVSS));

   initial begin
	 $write("*-* All Finished *-*\n");
	 $finish;
   end
endmodule

module sub (/*AUTOARG*/
   // Inouts
   AVDD, AVSS
   );
   // verilator no_inline_module
   inout AVDD;
   inout AVSS;
endmodule
