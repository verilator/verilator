// DESCRIPTION: Verilator: Preserved SVA property result signals
//
// This file ONLY is placed under the Creative Commons Public Domain, for any use,
// without warranty, 2026 by Verilator Authors. SPDX-License-Identifier: CC0-1.0

module t (
   input logic clk,
   input logic reset,
   input logic request,
   input logic grant
);
   named_assert: assert property (
      @(posedge clk) disable iff (reset) request |=> grant
   );

   named_assume: assume property (
      @(posedge clk) disable iff (reset) request |-> !grant
   );

   named_cover: cover property (
      @(posedge clk) disable iff (reset) request && grant
   );
   message_assert: assert property (@(posedge clk) request |-> grant)
      else $error("grant missing: request=%0b grant=%0b", request, grant);

   multi_assert: assert property (@(posedge clk) request |-> grant)
      else begin
         if (reset) $warning("reset active: %0b", reset);
         $error("grant missing again: %0b", grant);
      end
endmodule
