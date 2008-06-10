// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module liblib_a (/*AUTOARG*/);
   liblib_b b ();
endmodule

module liblib_b (/*AUTOARG*/);
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module liblib_c (/*AUTOARG*/);
   // Unused
   initial $stop;
   liblib_d d ();
endmodule

module liblib_d (/*AUTOARG*/);
   // Unused
   initial $stop;
endmodule
