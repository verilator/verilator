// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package a_pkg;
   typedef struct packed {
      int unsigned awidth;
      int unsigned dwidth;
   } cfg_t;
endpackage

module a_mod #(parameter a_pkg::cfg_t cfg=0)(
    input logic a
);
endmodule

module top();
   localparam a_pkg::cfg_t cfg = '{
      awidth : 16
      ,dwidth : 8
   };

   a_mod #(cfg) a_mod_inst(
      .a(1'b0)
   );

   initial begin
      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
