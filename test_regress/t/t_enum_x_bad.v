// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/);

   enum bit [1:0] { BADX = 2'b1x } BAD1;

   enum logic [3:0] { e0 = 4'b1xx1,
                      e1
                      } BAD2;

   initial begin
      $stop;
   end

endmodule
