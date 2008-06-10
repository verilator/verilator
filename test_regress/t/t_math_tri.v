// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/);

   reg [3:0] a;
   reg [99:0] x;

   initial begin
      a = 4'b010x;
      if (a[3:2] !== 2'b01) $stop;
      if (|a !== 1'b1) $stop;
      if (&a !== 1'b0) $stop;
      x = 100'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
