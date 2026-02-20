// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

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
