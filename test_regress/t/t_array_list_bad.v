// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   typedef struct packed {
      logic       t1;
      logic       t2;
      logic       t3;
   } type_t;
endpackage : pkg

module t
  (
   input logic sys_clk,
   input logic sys_rst_n,
   input logic sys_ena,

   input       pkg::type_t test_in,
   output      pkg::type_t test_out
   );

   import pkg::*;

   always_ff @(posedge sys_clk or negedge sys_rst_n) begin
      if (~sys_rst_n) begin
         test_out <= '{'0, '0, '0};
      end
      else begin
         if(sys_ena) begin
            test_out.t1 <= ~test_in.t1;
            test_out.t2 <= ~test_in.t2;
            test_out.t3 <= ~test_in.t3;
         end
         else begin
            test_out <= '{'0, '0}; /* Inconsistent array list; */
         end
      end
   end
endmodule: t
