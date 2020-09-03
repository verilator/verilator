// DESCRIPTION: Verilator: Verilog Test module
//
// The code here is used to trigger Verilator internal error
// "InitArray on non-array"
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Jie Xu.
// SPDX-License-Identifier: CC0-1.0

typedef logic [7:0]  mask_t [7:0];

// parameter logic [7:0] IMP_MASK[7:0] = '{8'hE1, 8'h03, 8'h07, 8'h3F, 8'h33, 8'hC3, 8'hC3, 8'h37};

parameter mask_t IMP_MASK = '{8'hE1, 8'h03, 8'h07, 8'h3F, 8'h33, 8'hC3, 8'hC3, 8'h37};

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   mask_t a;
   //logic [7:0] a[7:0];

   assign a = IMP_MASK;

endmodule
