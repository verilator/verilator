// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface Iface;
   logic clk = 1'b0, inp = 1'b0, io = 1'b0, out = 1'b0, out2 = 1'b0;
   clocking cb @(posedge clk);
       input #7 inp;
       output out;
       inout io;
   endclocking
   always @(posedge clk) inp <= 1'b1;
   always #5 clk <= ~clk;
   assign out2 = out;
endinterface

module main;
   initial begin
      #6;
      t.mod1.cb.io <= 1'b1;
      t.mod1.cb.out <= 1'b1;
      if (t.mod0.io != 1'b0) $stop;
      if (t.mod1.cb.io != 1'b0) $stop;
      if (t.mod1.cb.inp != 1'b0) $stop;
      @(posedge t.mod0.io)
      if ($time != 15) $stop;
      if (t.mod0.io != 1'b1) $stop;
      if (t.mod1.cb.io != 1'b0) $stop;
      #1
      if (t.mod0.cb.io != 1'b1) $stop;
      if (t.mod1.cb.io != 1'b1) $stop;
      if (t.mod1.cb.inp != 1'b1) $stop;
   end
   initial begin
      @(posedge t.mod0.out)
      if ($time != 15) $stop;
      if (t.mod1.out2 != 1'b1) $stop;
   end
endmodule

module t;
   main main1();
   Iface mod0();
   virtual Iface mod1 = mod0;
   initial begin
      #20;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
