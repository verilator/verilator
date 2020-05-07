// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by engr248.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   wire [31:0] in = 0;
   wire [31:0] out;

   Test test(
             .out(out[31:0]),
             .clk(clk),
             .in (in[31:0])
             );

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

interface Intf ();
endinterface

module Select
  #(
    parameter int NUM_MASTER = 1
    )
   (
    Intf Upstream,
    Intf Downstream[NUM_MASTER]
    );
endmodule

module Crossbar
 #(
   parameter int NUM_MASTER = 1,
   parameter int NUM_SLAVE = 1
   )
 (
  Intf Masters[NUM_MASTER]
  );

   Intf selectOut[(NUM_MASTER * (NUM_SLAVE))-1 : 0]();


   genvar i;

   for (i = 0; i < NUM_MASTER; i = i + 1) begin
      Select #(
               .NUM_MASTER(NUM_SLAVE)
               )
      select_inst (
                   .Upstream(Masters[i]),
                   // Following line seems to trigger a bad calculation for dimension where port
                   // is calculated as width 1 (correctly) and expression is calculated as NUM_MASTER*NUM_SLAVE rather than NUM_SLAVE
                   .Downstream(selectOut[(i)*(NUM_SLAVE) +: (NUM_SLAVE)])
                   // The following line works as intended and should be functionally identical to the above line
//                   .Downstream(selectOut[(i+1)*(NUM_SLAVE)-1 : i*(NUM_SLAVE)])
                   );
   end

endmodule

module Test
  (
   input             clk,
   input [31:0]      in,
   output reg [31:0] out
   );

   always @(posedge clk) begin
      out <= in;
   end

   Intf MST[10]();

   Crossbar #(
              .NUM_MASTER(10),
              .NUM_SLAVE(1)
              )
   xbar_inst (
              .Masters(MST)
              );

endmodule
