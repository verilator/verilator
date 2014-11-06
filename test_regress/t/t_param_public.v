// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

//bug505

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   a #(1) a1 ();
   b #(2) b2 ();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module a;
   parameter ONE /*verilator public*/ = 22;
   initial if (ONE != 1) $stop;
`ifdef VERILATOR
   initial if ($c32("ONE") != 1) $stop;
`endif
endmodule

module b #(
	   parameter TWO /*verilator public*/ = 22
	   );
   initial if (TWO != 2) $stop;
`ifdef VERILATOR
   initial if ($c32("TWO") != 2) $stop;
`endif
endmodule

//bug804
package p;
   localparam INPACK /*verilator public*/ = 6;
endpackage
