// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface Iface;
   logic clk = 1'b0, inp = 1'b0;
   clocking cb @(posedge clk);
       input #3 inp;
   endclocking
   always @(posedge clk) inp <= 1'b1;
   always #1 clk = ~clk;
endinterface

module main;
   initial begin
      #2;
      if (t.mod1.cb.inp != 1'b0) $stop;
      #4;
      if (t.mod1.cb.inp != 1'b1) $stop;
   end
endmodule

module t;
   main main1();
   Iface mod0();
   virtual Iface mod1 = mod0;
   initial begin
      #7;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
