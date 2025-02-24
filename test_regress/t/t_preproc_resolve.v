// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps
module top(/*AUTOARG*/
   input logic clk,
   input logic rst,
   output logic top_out
);
   submod u_submod (/*AUTOINST*/
      .clk (clk),
      .rst (rst),
      .out_signal(top_out)
   );
endmodule
