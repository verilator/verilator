// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

bit global_bit;

module t (clk, clk2);
   input clk;
   input clk2;
   integer cyc = 0;

   typedef struct packed {
      bit         b1;
      bit         b0;
   } strp_t;

   strp_t       v_strp, v_strp2;
   logic foo;

   logic [7:0]       unpacked_array[-7:0];

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      foo <= ~foo;
      v_strp.b0 <= cyc[0];
      v_strp2.b0 <= cyc[2];
      unpacked_array[0] = cyc[8:1];
      if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always @(posedge clk2) begin
      v_strp.b1 <= cyc[1];
      v_strp2.b1 <= cyc[3];
     for (int i = -1; i > -8; i--)
       unpacked_array[i] = cyc[7:0];
   end
endmodule
