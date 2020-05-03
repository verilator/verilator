// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t #(
           parameter [0:7] P = 8'd10
           )(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   int   cyc = 0;

   localparam [0:7] Q = 8'd20;

   logic [   0:  0] v_a = '0;
   logic [   0:  1] v_b = '0;
   logic [   0:  7] v_c = '0;
   logic [   0:  8] v_d = '0;
   logic [   0: 15] v_e = '0;
   logic [   0: 16] v_f = '0;
   logic [   0: 31] v_g = '0;
   logic [   0: 32] v_h = '0;
   logic [   0: 63] v_i = '0;
   logic [   0: 64] v_j = '0;
   logic [   0:127] v_k = '0;
   logic [   0:128] v_l = '0;
   logic [   0:255] v_m = '0;
   logic [   0:256] v_n = '0;
   logic [   0:511] v_o = '0;
   logic [  -1:  1] v_p = '0;
   logic [  -7:  7] v_q = '0;
   logic [ -15: 15] v_r = '0;
   logic [ -31: 31] v_s = '0;
   logic [ -63: 63] v_t = '0;
   logic [-127:127] v_u = '0;
   logic [-255:255] v_v = '0;

   always @(posedge clk) begin
      if (cyc == 0) begin
         v_a <= '1;
         v_b <= '1;
         v_c <= '1;
         v_d <= '1;
         v_e <= '1;
         v_f <= '1;
         v_g <= '1;
         v_h <= '1;
         v_i <= '1;
         v_j <= '1;
         v_k <= '1;
         v_l <= '1;
         v_m <= '1;
         v_n <= '1;
         v_o <= '1;
         v_p <= '1;
         v_q <= '1;
         v_r <= '1;
         v_s <= '1;
         v_t <= '1;
         v_u <= '1;
         v_v <= '1;
      end else begin
         v_a <= v_a << 1;
         v_b <= v_b << 1;
         v_c <= v_c << 1;
         v_d <= v_d << 1;
         v_e <= v_e << 1;
         v_f <= v_f << 1;
         v_g <= v_g << 1;
         v_h <= v_h << 1;
         v_i <= v_i << 1;
         v_j <= v_j << 1;
         v_k <= v_k << 1;
         v_l <= v_l << 1;
         v_m <= v_m << 1;
         v_n <= v_n << 1;
         v_o <= v_o << 1;
         v_p <= v_p << 1;
         v_q <= v_q << 1;
         v_r <= v_r << 1;
         v_s <= v_s << 1;
         v_t <= v_t << 1;
         v_u <= v_u << 1;
         v_v <= v_v << 1;
      end

      cyc <= cyc + 1;
      if (cyc == 2) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
