// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.

module t(/*AUTOARG*/);
   initial begin
      // Check error when this missing: $dumpfile("/should/not/be/opened");
      $dumpvars;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
