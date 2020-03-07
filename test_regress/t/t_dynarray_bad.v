// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.

module t (/*AUTOARG*/);

   integer a[];

   string  s;

   initial begin
      s = "str";
      a = new [s];  // Bad
   end

endmodule
