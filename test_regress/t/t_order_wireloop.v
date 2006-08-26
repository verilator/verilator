// $Id:$
// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//	$write("*-* All Finished *-*\n");
//	$finish
// on success, or $stop.
//
// **If you do not wish for your code to be released to the public
// please note it here**

module t (/*AUTOARG*/);

   wire  foo;
   wire  bar;

   // Oh dear.
   assign  foo = bar;
   assign  bar = foo;

endmodule
