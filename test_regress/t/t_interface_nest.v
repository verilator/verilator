// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017.
// SPDX-License-Identifier: CC0-1.0

interface if1;
   integer var1;
endinterface

interface if2;
   if1 i1 ();
   integer var2;
endinterface

module mod1
  (
   input clk,
   input integer modnum,  // Don't use parameter, want same module twice for better checking
   if2 foo
   );

   logic l1, l2;

   always_ff @(posedge clk) begin
      if (modnum==1) begin
         if (foo.i1.var1 != 1) $stop;
         if (foo.var2 != 2) $stop;
      end
      if (modnum==2) begin
         if (foo.i1.var1 != 1) $stop;
         if (foo.var2 != 2) $stop;
      end
   end

endmodule

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   if2 i2a ();
   if2 i2b ();

   assign i2a.i1.var1 = 1;
   assign i2a.var2 = 2;
   assign i2b.i1.var1 = 3;
   assign i2b.var2 = 4;

   mod1 mod1a
     (
      .modnum (1),
      .clk (clk),
      .foo (i2a)
      );

   mod1 mod1b
     (
      .modnum (2),
      .clk (clk),
      .foo (i2a)
      );

   integer cyc = 0;
   always_ff @(posedge clk) begin
      cyc <= cyc+1;
      if (cyc==2) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
