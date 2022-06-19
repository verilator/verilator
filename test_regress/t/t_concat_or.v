// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   i299,
   // Inputs
   i190, i191, i192, i193, i194, i195, i196, i197, i198, i199, i200, i201, i202,
   i203, i204, i205, i182, i183, i184, i185, i186, i187, i188, i189, i206, i282,
   i284, i286, i287, i289, i290, i294, i34, i288, i31, i296, i37, i38
   );
   input [3:0] i190;
   input [3:0] i191;
   input [3:0] i192;
   input [3:0] i193;
   input [3:0] i194;
   input [3:0] i195;
   input [3:0] i196;
   input [3:0] i197;
   input [3:0] i198;
   input [3:0] i199;
   input [3:0] i200;
   input [3:0] i201;
   input [3:0] i202;
   input [3:0] i203;
   input [3:0] i204;
   input [3:0] i205;
   input [3:0] i182;
   input [3:0] i183;
   input [3:0] i184;
   input [3:0] i185;
   input [3:0] i186;
   input [3:0] i187;
   input [3:0] i188;
   input [3:0] i189;
   input [3:0] i206;
   input [3:0] i282;
   input [3:0] i284;
   input [3:0] i286;
   input [3:0] i287;
   input [3:0] i289;
   input [3:0] i290;
   input [3:0] i294;
   input [3:0] i34;
   input [3:0] i288;
   input [3:0] i31;
   input [3:0] i296;
   input [3:0] i37;
   input [3:0] i38;

   output [3:0] i299;
   assign  i299 = { i296[2:0] | i31[3:1] | i282[3:1] | i284[3:1] | i34[3:1]
                    | i286[3:1] | i287[3:1] | i37[3:1] | i38[3:1]
                    | i288[3:1] | i289[3:1] | i290[3:1] | i182[3:1]
                    | i183[3:1] | i184[3:1] | i185[3:1] | i186[3:1]
                    | i187[3:1] | i188[3:1] | i189[3:1] | i190[3:1]
                    | i191[3:1] | i192[3:1] | i193[3:1] | i194[3:1]
                    | i195[3:1] | i196[3:1] | i197[3:1] | i198[3:1]
                    | i199[3:1] | i200[3:1] | i201[3:1] | i202[3:1]
                    | i203[3:1] | i204[3:1] | i205[3:1] | i206[3:1]
                    ,
                    i294[0] | i289[0] | i290[0] | i182[0] | i183[0]
                    | i184[0] | i185[0] | i186[0] | i187[0] | i188[0]
                    | i189[0] | i190[0] | i191[0] | i192[0] | i193[0]
                    | i194[0] | i195[0] | i196[0] | i197[0] | i198[0]
                    | i199[0] | i200[0] | i201[0] | i202[0] | i203[0]
                    | i204[0] | i205[0] | i206[0] };

endmodule
