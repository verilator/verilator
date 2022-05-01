// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Also check that SystemC is ordering properly
// verilator lint_on IMPERFECTSCH

module t (/*AUTOARG*/
   // Outputs
   o1, o8, o16, o32, o64, o65, o128, o513, o1a2, o94a3, obv1, obv16, obv1_vlt, obv16_vlt,
   // Inputs
   clk, i1, i8, i16, i32, i64, i65, i128, i513, i1a2, i94a3, ibv1, ibv16, ibv1_vlt, ibv16_vlt
   );

   input clk;

   input         i1;
   input [7:0]   i8;
   input [15:0]  i16;
   input [31:0]  i32;
   input [63:0]  i64;
   input [64:0]  i65;
   input [127:0] i128;
   input [512:0] i513;
   input         i1a2 [1:0];
   input [93:0]  i94a3 [2:0];

   output logic           o1;
   output logic [7:0]   o8;
   output logic [15:0]  o16;
   output logic [31:0]  o32;
   output logic [63:0]  o64;
   output logic [64:0]  o65;
   output logic [127:0] o128;
   output logic [512:0] o513;
   output logic           o1a2 [1:0];
   output logic [93:0]  o94a3 [2:0];

   input [0:0]   ibv1 /*verilator sc_bv*/;
   input [15:0]    ibv16 /*verilator sc_bv*/;
   input [0:0]     ibv1_vlt;
   input [15:0]     ibv16_vlt;

   output logic [0:0]   obv1 /*verilator sc_bv*/;
   output logic [15:0]  obv16 /*verilator sc_bv*/;
   output logic [0:0]   obv1_vlt;
   output logic [15:0]  obv16_vlt;

   always @ (posedge clk) begin
      o1 <= i1;
      o8 <= i8;
      o16 <= i16;
      o32 <= i32;
      o64 <= i64;
      o65 <= i65;
      o128 <= i128;
      o513 <= i513;
      obv1 <= ibv1;
      obv16 <= ibv16;
      obv1_vlt <= ibv1_vlt;
      obv16_vlt <= ibv16_vlt;
      o1a2 <= i1a2;
      o94a3 <= i94a3;
   end

endmodule
