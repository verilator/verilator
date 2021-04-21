// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
   logic         car_enable;
   logic [3-1:0] car_rpv;
   logic [2-1:0] car_sn;
} car_s;

module t (/*AUTOARG*/
   // Outputs
   action,
   // Inputs
   rsp
   );
   input rsp;
   output action;
   car_s  rsp;
   car_s  action;
   always @(*) begin
      action = rsp;
      if (rsp.car_enable == 1'b1) begin
         action.car_rpv[ action.car_sn] = 1'b0;    // causing problem
         // OK
         //action.car_rpv[ rsp.car_sn] = 1'b0;
      end
   end
endmodule
