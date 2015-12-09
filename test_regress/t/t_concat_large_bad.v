// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Wilson Snyder.

module t (/*AUTOARG*/);

   wire [32767:0] a = {32768{1'b1}};

   initial begin
      $stop;
   end

endmodule
