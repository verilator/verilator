// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Wilson Snyder.

module t (/*AUTOARG*/);
   initial begin
      $display("Merge:");
      $write("This ");
      $write("should ");
      $display("merge");
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
