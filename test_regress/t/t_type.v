// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.

module t(/*AUTOARG*/);

   real x;
   real y;
   var type(x+y) z;

   initial begin
      x = 1.2;
      y = 2.3;
      z = x + y;
      if (z != (1.2+2.3)) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
