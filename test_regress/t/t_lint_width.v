// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t ();

   // This isn't a width violation, as +/- 1'b1 is a common idiom
   // that's fairly harmless
   wire [4:0] five = 5'd5;
   wire [4:0] suma = five + 1'b1;
   wire [4:0] sumb = 1'b1 + five;
   wire [4:0] sumc = five - 1'b1;

endmodule
