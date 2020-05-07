// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Peter Monsson.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   Test test (/*AUTOINST*/
              // Inputs
              .clk                      (clk));

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module Test
  (
   input clk
   );

`ifdef FAIL_ASSERT_1
   assert property (
     @(posedge clk)
     1 |-> 0
   ) else $display("[%0t] wrong implication", $time);
`endif

   assert property (
     @(posedge clk)
     1 |-> 1
   );

   assert property (
     @(posedge clk)
     0 |-> 0
   );

   assert property (
     @(posedge clk)
     0 |-> 1
   );

endmodule
