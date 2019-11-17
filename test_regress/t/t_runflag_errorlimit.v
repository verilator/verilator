// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t;
   initial begin
      $error("One");
      $error("Two");
      $error("Three");
      $error("Four");
      $error("Five");
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
