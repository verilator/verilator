// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Wilson Snyder.

// Should have been:
//module t #(

module t
  (
   FOO=1
   ) (
      output bar
      );

   assign bar = FOO;

endmodule
