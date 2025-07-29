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

   logic logic_unused;
   // CHECK_COVER(-1,"top.t","logic_unused",0)

   bit bit_unused;
   // CHECK_COVER(-1,"top.t","bit_unused",0)

   logic logic_always_0;
   // CHECK_COVER(-1,"top.t","logic_always_0",0)

   bit bit_always_0;
   // CHECK_COVER(-1,"top.t","bit_always_0",0)

   logic logic_always_1;
   // CHECK_COVER(-1,"top.t","logic_always_1",0)

   bit bit_always_1;
   // CHECK_COVER(-1,"top.t","bit_always_1",1)

   logic logic_initial_0;
   // CHECK_COVER(-1,"top.t","logic_initial_0",0)

   bit bit_initial_0;
   // CHECK_COVER(-1,"top.t","bit_initial_0",0)

   logic logic_initial_1;
   // CHECK_COVER(-1,"top.t","logic_initial_1",0)

   bit bit_initial_1;
   // CHECK_COVER(-1,"top.t","bit_initial_1",1)

   initial begin
      cyc = 1;
      logic_initial_0 = 0;
      bit_initial_0 = 0;
      logic_initial_1 = 1;
      bit_initial_1 = 1;
   end

   always @(posedge clk) begin
      logic_always_0 = 0;
      bit_always_0 = 0;
      logic_always_1 = 1;
      bit_always_1 = 1;

      if (cyc != 0) cyc <= cyc + 1;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
