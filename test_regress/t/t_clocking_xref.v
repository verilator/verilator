// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module mod;
   logic clk = 1'b0;
   logic inp = 1'b0;
   clocking cb @(posedge clk);
       input #3 inp;
   endclocking
   always @(posedge clk) inp <= 1'b1;
   always #1 clk = ~clk;
endmodule

module main;
   logic clk = 1'b0;
   logic inp = 1'b0;
   always begin
      #2
      if (t.mod1.cb.inp != 1'b0) $stop;
      if (t.main1.cbb.inp != 1'b0) $stop;
      if (t.main2.cbb.inp != 1'b0) $stop;
      #4;
      if (t.mod1.cb.inp != 1'b1) $stop;
      if (t.main1.cbb.inp != 1'b1) $stop;
      if (t.main2.cbb.inp != 1'b1) $stop;
   end
   clocking cbb @(posedge clk);
       input #3 inp;
   endclocking
   always @(posedge clk) inp <= 1'b1;
   always #1 clk = ~clk;
endmodule

module t;
   main main1();
   mod mod1();
   main main2();
   initial begin
      #7;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
