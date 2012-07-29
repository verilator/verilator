// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module x;

   typedef struct {
      int 	  a;
   } notpacked_t;

   typedef struct packed {
      notpacked_t	a;
   } ispacked_t;

endmodule
