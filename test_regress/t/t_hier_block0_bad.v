// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020-2024 Yutetsu TAKATSUKASA and Antmicro
// SPDX-License-Identifier: Unlicense

`define HIER_BLOCK /*verilator hier_block*/

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [7:0] out0;
   wire [7:0] out1;
   int count = 0;

   // unpacked array cannot be passed to hierarchical block
   localparam logic UNPACKED[0:1] = '{1'b1, 1'b0};
   sub0 #(UNPACKED) i_sub0(.clk(clk), .in(8'(count)), .out(out0));
   sub1 #(.T(logic[7:0])) i_sub1(.in(out0), .out(out1));

   always_ff @(posedge clk) begin
      // dotted access under hierarchical block is not allowed ...
      $display("%d i_sub0.ff: %d", count, i_sub0.ff);
      $display("%d i_sub0.i_sub.out: %d", count, i_sub0.i_sub.out);
      // ... Except for ports on a dierct hierarchical child
      $display("%d i_sub0.out: %d", count, i_sub0.out);
      $display("%d out1: %d", count, out1);
      if (count == 16) begin
         if (out1 == 15) begin
             $write("*-* All Finished *-*\n");
             $finish;
         end else begin
             $write("Missmatch\n");
             $stop;
         end
      end
      count <= count + 1;
   end

endmodule

module sub0 #(
   parameter logic UNPACKED[0:1] = '{1'b0, 1'b1}
   ) (
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK

   logic [7:0] ff;

   always_ff @(posedge clk) ff <= in;
   assign out = ff;

   logic [7:0] gg;
   sub0_sub0 i_sub(.in(ff), .out(gg));

   always_ff @(posedge clk) begin
      // dotted access under hierarchical block is not allowed ...
      $display("%m: i_sub.x: %d", i_sub.x);
      // ... Except for ports on a direct hierarchical child
      $display("%m: i_sub.out: %d", i_sub.out);
   end
endmodule

module sub1 #(
   parameter type T = logic
   ) (
    input wire T in, output wire T out); `HIER_BLOCK
   assign out = in;

   sub1_sub #(T) sub(in, out);
endmodule

module sub0_sub0 (
  input  wire [7:0] in,
  output wire [7:0] out
);
  `HIER_BLOCK
  wire [7:0] x = in + 1;
  assign out = x;
endmodule
