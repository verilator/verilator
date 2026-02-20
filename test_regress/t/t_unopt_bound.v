// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Jue Xu
// SPDX-License-Identifier: CC0-1.0

// bug630

module t ( clk, out );
   input clk;
   output out;

   reg      a;
   reg      b;

   typedef struct packed {
      logic       config_a;
      logic       config_b;
   } param_t;
   // verilator lint_off UNOPTFLAT
   param_t conf [1:2] ;
   // verilator lint_on UNOPTFLAT

   always @ (posedge clk) begin
      conf[2].config_b <= a;
      $write("*-* All Finished *-*\n");
      $finish;
   end
   always @ (posedge conf[2].config_b) begin
      a = conf[2].config_a;
   end
endmodule
