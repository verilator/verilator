// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   typedef enum logic [2:0] {
                             TWO  = 2,
                             THREE   = 3
                             } enum_t;
endpackage

module t;
   localparam L_TWO = pkg::TWO;
   initial begin
      if (L_TWO != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
