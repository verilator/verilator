// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps
module submod(/*AUTOARG*/
   input logic clk,
   input logic rst,
   output logic out_signal
);
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         out_signal <= 1'b0;
      end else begin
         out_signal <= ~out_signal;
      end
   end
endmodule
