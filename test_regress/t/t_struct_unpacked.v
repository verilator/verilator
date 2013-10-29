// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module x;

   // verilator lint_off UNPACKED
   typedef struct {
      int 	  a;
   } notpacked_t;
   // verilator lint_on UNPACKED

   typedef struct packed {
      notpacked_t b;
   } ispacked_t;

   ispacked_t p;

   initial begin
      p.b = 1;
      if (p.b != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
