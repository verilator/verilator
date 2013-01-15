// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

// bug474
package verb_pkg;
   typedef enum int {VERB_I, 
		     VERB_W} Verb_t;
   Verb_t  verb = VERB_I;
   string message = " ";
endpackage

module t;
   import verb_pkg::*;

   string message  = "*x*";
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
