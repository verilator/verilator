// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t(clk);
   input clk;

   bit toggle;
   // CHECK_COVER(-1,"top.t","toggle",0)

   bit toggle_0 = 0;
   // CHECK_COVER(-1,"top.t","toggle_0",0)

   bit toggle_1 = 1;
   // CHECK_COVER(-1,"top.t","toggle_1",0)

   bit toggle_always_0;
   bit toggle_always_1;

   always @(posedge clk) begin
      toggle_always_0 = 0;
      // CHECK_COVER(-1,"top.t","toggle_always_0",0)

      toggle_always_1 = 1;
      // CHECK_COVER(-1,"top.t","toggle_always_1",0)

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
