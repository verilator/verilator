// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Yutetsu TAKATSUKASA
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t(input wire clk);

   logic [2:0] v = 3'd0;
   logic [2:0] v_plus_1;

   always_comb begin : blk_comb
      if (v[0]) begin : blk_if
          automatic logic [2:0] tmp0;  // This automatic variable cannot be a latch
          tmp0 = v + 3'd1;
          v_plus_1 = tmp0;
      end else begin : blk_else
          v_plus_1 = v | 3'd1;
      end
   end

   always @(posedge clk) begin : blk_ff
      automatic logic [2:0] tmp_auto;
      tmp_auto = v_plus_1;
      v <= tmp_auto;
      $display("v:%d", v);
  end

endmodule
