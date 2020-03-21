// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Alex Solomatnikov.
// SPDX-License-Identifier: CC0-1.0

typedef logic [$clog2(26+1)-1:0] way_cnt_t;

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input logic clk;
   int     cyc;

   //bug795
   way_cnt_t completed_cnt   [31:0][1:0];
   way_cnt_t completed_cnt_dp        [1:0];

   assign completed_cnt_dp = completed_cnt[id];

   always_ff @(posedge clk) begin
      completed_cnt[id] <= completed_cnt_dp + 1;
   end

   // bug796
   logic [4:0] id;
   logic [39:0] way_mask;
   logic [39:0] addr[31:0][1:0];
   always_ff @(posedge clk) begin
      cyc <= cyc + 1;
      id <= cyc[4:0];
      if (cyc==1) begin
         way_mask <= '0;
         id <= 1;
      end
      else if (cyc==2) begin
         assert((addr[id] & way_mask) == 0);
      end
  end
endmodule
