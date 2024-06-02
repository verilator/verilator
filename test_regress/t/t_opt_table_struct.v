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

   struct packed {
      bit [31:0] a;
      bit [15:0] b;
      bit [ 7:0] c;
   } s;

   reg [2:0]     cyc;

   initial cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   always @* begin
      case (cyc)
        3'b000: s = {32'd0, 16'd1, 8'd2};
        3'b001: s = {32'd1, 16'd2, 8'd3};
        3'b010: s = {32'd2, 16'd3, 8'd4};
        3'b100: s = {32'd4, 16'd5, 8'd6};
        3'b101: s = {32'd5, 16'd6, 8'd7};
        default: s = '0;
      endcase
   end

   always @(posedge clk) begin
      $display("cyle %d = { %d, %d, %d }", cyc, s.a, s.b, s.c);
      if (cyc == 7) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
