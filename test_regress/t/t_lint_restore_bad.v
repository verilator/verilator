// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t ();

   reg [3:0] four;
   reg [4:0] five;

   // verilator lint_save

   // verilator lint_off WIDTH
   initial four = 64'h1;

   // verilator lint_restore

   initial five = 64'h1;

   initial $stop;

endmodule
