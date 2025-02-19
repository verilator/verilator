// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module vip_snitch_cluster
  #(parameter realtime ClkPeriod = 10ns)
  (output logic clk_o);

   initial begin
      forever begin
         clk_o = 1;
         #(ClkPeriod/2);
         clk_o = 0;
         #(ClkPeriod/2);
      end
   end

   initial begin
      #(ClkPeriod*100);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module t;
    logic clk;

    vip_snitch_cluster #(
        .ClkPeriod(1ns)
    ) vip (
        .clk_o(clk)
    );

endmodule
