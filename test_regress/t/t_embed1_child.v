// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_embed1_child (/*AUTOARG*/
   // Outputs
   bit_out, vec_out, wide_out, did_init_out,
   // Inputs
   clk, bit_in, vec_in, wide_in, is_ref
   );

   input  clk;
   input  bit_in;
   output bit_out;
   input  [30:0] vec_in;
   output logic [30:0] vec_out;
   input  [123:0] wide_in;
   output logic [123:0] wide_out;
   output 	  did_init_out;

   input 	  is_ref;

   reg did_init; initial did_init = 0;
   initial begin
      did_init = 1;
   end

   reg did_final; initial did_final = 0;
   final begin
      did_final = 1;
      if (!is_ref) $write("*-* All Finished *-*\n");
      //$finish is in parent
   end

   // Note async use!
   wire bit_out = bit_in;
   wire did_init_out = did_init;

   always @ (posedge clk) begin
      vec_out <= vec_in;
      wide_out <= wide_in;
   end

endmodule
