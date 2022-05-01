// DESCRIPTION: Verilator: Verilog Test module
//
// IEEE 1800-2009 requires that any local definitions take precedence over
// definitions in wildcard imported packages (section 26.3). Thus the code
// below is valid SystemVerilog.
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty, 2013 by Jie Xu.
// SPDX-License-Identifier: CC0-1.0

package defs;
   parameter NUMBER = 8;
   localparam NUM = NUMBER;
endpackage


module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   import defs::*;

   // This also fails if we use localparam
   parameter NUM = 32;

   // Check we have the right definition
   always @(posedge clk) begin
      if (NUM == 32) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $stop;
      end
   end

endmodule
