// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   Test test (/*AUTOINST*/
              // Inputs
              .clk                      (clk),
              .cyc                      (cyc[31:0]));

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
   input clk,
   input [31:0] cyc
   );

`ifdef FAIL_ASSERT_1
   assert property (@(posedge clk) cyc==3)
     else $display("cyc != 3, cyc == %0d", cyc);
   assume property (@(posedge clk) cyc==3)
     else $display("cyc != 3, cyc == %0d", cyc);
`endif

`ifdef FAIL_ASSERT_2
   assert property (@(posedge clk) cyc!=3);
   assume property (@(posedge clk) cyc!=3);
`endif

   assert property (@(posedge clk) cyc < 100);
   assume property (@(posedge clk) cyc < 100);

   restrict property (@(posedge clk) cyc==1);  // Ignored in simulators

// Unclocked is not supported:
//   assert property (cyc != 6);

endmodule
