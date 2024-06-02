// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_param_first_a (/*AUTOARG*/
   // Outputs
   varwidth, par
   );

   parameter X = 1;
   parameter FIVE = 0; // Overridden
   parameter TWO = 2;

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [4:0]         par;                    // From b of t_param_first_b.v
   output [X:0]         varwidth;               // From b of t_param_first_b.v
   // End of automatics

   t_param_first_b #(X,FIVE,TWO) b
     (/*AUTOINST*/
      // Outputs
      .par                              (par[4:0]),
      .varwidth                         (varwidth[X:0]));

endmodule
