// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk_0, clk_1, clk_2, clk_3, clk_4, clk_5, clk_6, clk_7, clk_8, clk_9, clk_10,
   clk_11, clk_12, clk_13, clk_14, clk_15, clk_16, clk_17, clk_18, clk_19,
   rstn_0, rstn_1, rstn_2, rstn_3, rstn_4, rstn_5, rstn_6, rstn_7, rstn_8,
   rstn_9, rstn_10, rstn_11, rstn_12, rstn_13, rstn_14, rstn_15, rstn_16,
   rstn_17, rstn_18, rstn_19
   );

   input clk_0;
   input clk_1;
   input clk_2;
   input clk_3;
   input clk_4;
   input clk_5;
   input clk_6;
   input clk_7;
   input clk_8;
   input clk_9;
   input clk_10;
   input clk_11;
   input clk_12;
   input clk_13;
   input clk_14;
   input clk_15;
   input clk_16;
   input clk_17;
   input clk_18;
   input clk_19;
   input rstn_0;
   input rstn_1;
   input rstn_2;
   input rstn_3;
   input rstn_4;
   input rstn_5;
   input rstn_6;
   input rstn_7;
   input rstn_8;
   input rstn_9;
   input rstn_10;
   input rstn_11;
   input rstn_12;
   input rstn_13;
   input rstn_14;
   input rstn_15;
   input rstn_16;
   input rstn_17;
   input rstn_18;
   input rstn_19;

   // verilator lint_off MULTIDRIVEN
   output reg out [0:29-1];

   always_ff @(posedge clk_0, negedge rstn_0) if ((rstn_0 == 0)) out[0] <= 0;
   always_ff @(posedge clk_1, negedge rstn_1) if ((rstn_1 == 0)) out[1] <= 0;
   always_ff @(posedge clk_2, negedge rstn_2) if ((rstn_2 == 0)) out[2] <= 0;
   always_ff @(posedge clk_3, negedge rstn_3) if ((rstn_3 == 0)) out[3] <= 0;
   always_ff @(posedge clk_4, negedge rstn_4) if ((rstn_4 == 0)) out[4] <= 0;
   always_ff @(posedge clk_5, negedge rstn_5) if ((rstn_5 == 0)) out[5] <= 0;
   always_ff @(posedge clk_6, negedge rstn_6) if ((rstn_6 == 0)) out[6] <= 0;
   always_ff @(posedge clk_7, negedge rstn_7) if ((rstn_7 == 0)) out[7] <= 0;
   always_ff @(posedge clk_8, negedge rstn_8) if ((rstn_8 == 0)) out[8] <= 0;
   always_ff @(posedge clk_9, negedge rstn_9) if ((rstn_9 == 0)) out[9] <= 0;
   always_ff @(posedge clk_10, negedge rstn_10) if ((rstn_10 == 0)) out[10] <= 0;
   always_ff @(posedge clk_11, negedge rstn_11) if ((rstn_11 == 0)) out[11] <= 0;
   always_ff @(posedge clk_12, negedge rstn_12) if ((rstn_12 == 0)) out[12] <= 0;
   always_ff @(posedge clk_13, negedge rstn_13) if ((rstn_13 == 0)) out[13] <= 0;
   always_ff @(posedge clk_14, negedge rstn_14) if ((rstn_14 == 0)) out[14] <= 0;
   always_ff @(posedge clk_15, negedge rstn_15) if ((rstn_15 == 0)) out[15] <= 0;
   always_ff @(posedge clk_16, negedge rstn_16) if ((rstn_16 == 0)) out[16] <= 0;
   always_ff @(posedge clk_17, negedge rstn_17) if ((rstn_17 == 0)) out[17] <= 0;
   always_ff @(posedge clk_18, negedge rstn_18) if ((rstn_18 == 0)) out[18] <= 0;
   always_ff @(posedge clk_19, negedge rstn_19) if ((rstn_19 == 0)) out[19] <= 0;

endmodule
