// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   typedef logic [3:0] mc_t;
   typedef mc_t tocast_t;

   typedef struct packed {
      logic [15:0] data;
   } packed_t;

   packed_t pdata;
   assign pdata.data = 16'h1234;
   logic [7:0] logic8bit;
   assign logic8bit = $bits(logic8bit)'(pdata >> 8);

   mc_t o;

   logic [15:0] allones = 16'hffff;
   parameter FOUR = 4;

   // bug925
   localparam [6:0] RESULT = 7'((6*9+92)%96);

   logic signed [14:0] samp0 = 15'h0000;
   logic signed [14:0] samp1 = 15'h0000;
   logic signed [14:0] samp2 = 15'h6000;
   logic signed [11:0] coeff0 = 12'h009;
   logic signed [11:0] coeff1 = 12'h280;
   logic signed [11:0] coeff2 = 12'h4C5;
   logic signed [26:0] mida =    ((27'(coeff2 * samp2) >>> 11));
   // verilator lint_off WIDTH
   logic signed [26:0] midb = 15'((27'(coeff2 * samp2) >>> 11));
   // verilator lint_on WIDTH
   logic signed [14:0] outa = 15'((27'(coeff0 * samp0) >>> 11) + // 27' size casting in order for intermediate result to not be truncated to the width of LHS vector
				  (27'(coeff1 * samp1) >>> 11) +
				  (27'(coeff2 * samp2) >>> 11)); // 15' size casting to avoid synthesis/simulator warnings

   initial begin
      if (logic8bit != 8'h12) $stop;
      if (4'shf > 4'sh0) $stop;
      if (signed'(4'hf) > 4'sh0) $stop;
      if (4'hf < 4'h0) $stop;
      if (unsigned'(4'shf) < 4'h0) $stop;
      if (4'(allones) !== 4'hf) $stop;
      if (6'(allones) !== 6'h3f) $stop;
      if ((4)'(allones) !== 4'hf) $stop;
      if ((4+2)'(allones) !== 6'h3f) $stop;
      if ((4-2)'(allones) !== 2'h3) $stop;
      if ((FOUR+2)'(allones) !== 6'h3f) $stop;
      if (50 !== RESULT) $stop;

      o = tocast_t'(4'b1);
      if (o != 4'b1) $stop;

      if (15'h6cec != outa) $stop;
      if (27'h7ffecec != mida) $stop;
      if (27'h7ffecec != midb) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
