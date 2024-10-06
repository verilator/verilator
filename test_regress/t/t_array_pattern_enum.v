// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
   typedef enum {
      RED=0,
      GREEN=1,
      BLUE=2
   } color_t;

   typedef struct {
      color_t pixels[32];
   } line_t;

   typedef struct {
      line_t line[32];
   } screen_t;
endpackage

module t;
   Pkg::screen_t screen;

   initial begin
      screen = '{ default: '0, Pkg::color_t: Pkg::RED};
      $display("%p", screen);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
