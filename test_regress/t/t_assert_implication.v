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
              .clk(clk),
              .cyc(cyc));

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
`ifdef TEST_VERBOSE
         $display("cyc=%0d", cyc);
`endif
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module Test
  (
   input clk,
   input integer cyc
   );

`ifdef FAIL_ASSERT_1
   assert property (
     @(posedge clk)
     1 |-> 0
   ) else $display("[%0t] wrong implication", $time);

   assert property (
     @(posedge clk)
     1 |=> 0
   ) else $display("[%0t] wrong implication", $time);

   assert property (
     @(posedge clk)
     cyc%3==1 |=> cyc%3==1
   ) else $display("[%0t] wrong implication (step)", $time);

   assert property (
     @(posedge clk)
     cyc%3==1 |=> cyc%3==0
   ) else $display("[%0t] wrong implication (step)", $time);

   assert property (
     @(posedge clk) disable iff (cyc == 3)
     (cyc == 4) |=> 0
   ) else $display("[%0t] wrong implication (disable)", $time);

   assert property (
     @(posedge clk) disable iff (cyc == 6)
     (cyc == 4) |=> 0
   ) else $display("[%0t] wrong implication (disable)", $time);

`endif

   // Test |->
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

   // Test |=>
   assert property (
     @(posedge clk)
     1 |=> 1
   );

   assert property (
     @(posedge clk)
     0 |=> 0
   );

   assert property (
     @(posedge clk)
     0 |=> 1
   );

   // Test correct handling of time step in |=>
   assert property (
     @(posedge clk)
     cyc%3==1 |=> cyc%3==2
   );

   // Test correct handling of disable iff
   assert property (
     @(posedge clk) disable iff (cyc < 3)
     1 |=> cyc > 3
   );

   // Test correct handling of disable iff in current cycle
   assert property (
     @(posedge clk) disable iff (cyc == 4)
     (cyc == 4) |=> 0
   );

   // Test correct handling of disable iff in previous cycle
   assert property (
     @(posedge clk) disable iff (cyc == 5)
     (cyc == 4) |=> 0
   );

endmodule
