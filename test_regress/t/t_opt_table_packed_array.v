// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [3:0][3:0] a;

   reg [2:0]        cyc;

   initial cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   always @* begin
      case (cyc)
        3'b000: a = {4'd0, 4'd1, 4'd2, 4'd3};
        3'b001: a = {4'd1, 4'd2, 4'd3, 4'd4};
        3'b010: a = {4'd4, 4'd3, 4'd4, 4'd5};
        3'b100: a = {4'd4, 4'd5, 4'd6, 4'd7};
        3'b101: a = {4'd5, 4'd6, 4'd7, 4'd8};
        default: a = {4{4'hf}};
      endcase
   end

   always @(posedge clk) begin
      $display("cyle %d = { %d, %d, %d, %d }", cyc, a[0], a[1], a[2], a[3]);
      if (cyc == 7) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
