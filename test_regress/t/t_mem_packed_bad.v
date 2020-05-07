// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc = 0;

   logic [1:0][27:0]       ch01;
   logic [1:0][27:0]       ch02;
   logic [1:0][27:0]       ch03;
   logic      [27:0]       ch04[1:0];

   /* verilator lint_off WIDTH */
   always @ (posedge clk) begin
      // LHS is a 2D packed array, RHS is 1D packed or Const. Allowed now.
      ch01                  <= {{2{28'd4}}};
      ch02                  <= {{2{cyc}}};
      ch03                  <= 56'd0;
      // LHS is 1D packed, 1D unpacked, this should never work.
      ch04                  <= 56'd0;
      $display("ch01: %0x %0x", ch01[0], ch01[1]);
      $display("ch01: %0x %0x", ch02[0], ch02[1]);
      $display("ch01: %0x %0x", ch03[0], ch03[1]);
      $display("ch01: %0x %0x", ch04[0], ch04[1]);
   end
   /* verilator lint_on WIDTH */

endmodule
