// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t(clk);
   // verilator coverage_off
   input clk;
   integer cyc;
   // verilator coverage_on

   logic toggle;
   // CHECK_COVER(-1,"top.t","toggle",0)

   logic toggle_always_0;
   // CHECK_COVER(-1,"top.t","toggle_always_0",0)

   logic toggle_always_1;
   // CHECK_COVER(-1,"top.t","toggle_always_1",0)

   logic toggle_initial_0;
   // CHECK_COVER(-1,"top.t","toggle_initial_0",0)

   logic toggle_initial_1;
   // CHECK_COVER(-1,"top.t","toggle_initial_1",0)

   initial begin
      cyc = 1;
      toggle_initial_0 = 0;
      toggle_initial_1 = 1;
   end

   always @(posedge clk) begin
      toggle_always_0 = 0;
      toggle_always_1 = 1;

      if (cyc != 0) cyc <= cyc + 1;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
