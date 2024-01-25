// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// See issue #2855

package Pkg;

   typedef enum int unsigned {
      MODE10 = 10
   } mode_t;

   typedef struct packed {
      bit    u;
      mode_t a;
      bit    b;
   } foo_t;

   localparam foo_t FOO0 = '{a: 0,      b: 1'b1, u: 1'b1};

   localparam foo_t FOO1 = '{a: MODE10, b: 1'b1, u: 1'b1};

endpackage

module t(/*AUTOARG*/);

   initial begin
      //if (sum !== `EXPECTED_SUM) $stop;
      if (Pkg::FOO0 != {1'b1, 32'd0, 1'b1}) $stop;
      if (Pkg::FOO1 != {1'b1, 32'd10, 1'b1}) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
