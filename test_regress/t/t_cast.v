// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface intf;
   typedef logic [7:0] octet;
   typedef octet [1:0] word;
   octet [1:0] octets;
   word [1:0] words;
endinterface

module t;

   typedef logic [3:0] mc_t;
   typedef mc_t tocast_t;
   typedef logic [2:0] [7:0] two_dee_t;

   typedef struct packed {
      logic [15:0] data;
   } packed_t;
   typedef struct packed {
      logic [31:0] data;
   } packed2_t;

   typedef enum [15:0] {
      ONE = 1
   } enum_t;

   packed_t pdata;
   packed_t pdata_reg;
   packed2_t pdata2_reg;
   assign pdata.data = 16'h1234;
   logic [7:0] logic8bit;
   assign logic8bit = $bits(logic8bit)'(pdata >> 8);

   mc_t o;
   enum_t e;

   intf the_intf();

   logic [15:0] allones = 16'hffff;
   parameter FOUR = 4;

   localparam two_dee_t two_dee = two_dee_t'(32'habcdef);

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

   logic one = 1'b1;
   logic [32:0] b33 = {32'(0), one};
   logic [31:0] b32 = {31'(0), one};

   logic [31:0] thirty_two_bits;
   two_dee_t two_dee_sig;

   initial begin
      if (logic8bit != 8'h12) $stop;
      if (4'shf > 4'sh0) $stop;
      if (signed'(4'hf) > 4'sh0) $stop;
      if (4'hf < 4'h0) $stop;
      if (unsigned'(4'shf) < 4'h0) $stop;
      if (const'(4'shf) !== 4'shf) $stop;
      if (4'(allones) !== 4'hf) $stop;
      if (6'(allones) !== 6'h3f) $stop;
      if ((4)'(allones) !== 4'hf) $stop;
      if ((4+2)'(allones) !== 6'h3f) $stop;
      if ((4-2)'(allones) !== 2'h3) $stop;
      if ((FOUR+2)'(allones) !== 6'h3f) $stop;
      if (50 !== RESULT) $stop;

      e = ONE;
      if (e != 1) $stop;
      if (e != ONE) $stop;
      e = enum_t'(ONE);
      if (e != ONE) $stop;
      e = enum_t'(16'h1);
      if (e != ONE) $stop;
      pdata_reg.data = 1;
      e = enum_t'(pdata_reg);
      if (e != ONE) $stop;

      o = tocast_t'(4'b1);
      if (o != 4'b1) $stop;

      the_intf.octets = 16'd1;
      pdata_reg = packed_t'(the_intf.octets);
      if (pdata_reg.data != 16'd1) $stop;

      the_intf.words = 32'd1;
      pdata2_reg = packed2_t'(the_intf.words);
      if (pdata2_reg.data != 32'd1) $stop;

      if (15'h6cec != outa) $stop;
      if (27'h7ffecec != mida) $stop;
      if (27'h7ffecec != midb) $stop;

      if (b33 != 33'b1) $stop;
      if (b32 != 32'b1) $stop;

      if (two_dee[0] != 8'hef) $stop;
      if (two_dee[1] != 8'hcd) $stop;
      if (two_dee[2] != 8'hab) $stop;

      thirty_two_bits = 32'h123456;
      two_dee_sig = two_dee_t'(thirty_two_bits);

      if (two_dee_sig[0] != 8'h56) $stop;
      if (two_dee_sig[1] != 8'h34) $stop;
      if (two_dee_sig[2] != 8'h12) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
