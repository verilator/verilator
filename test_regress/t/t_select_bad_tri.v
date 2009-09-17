// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/);

   reg [72:1] in;
   initial begin
      if (in[(   (1'h0 / 1'b0)   )+:71] != 71'h0) $stop;
   end

endmodule
