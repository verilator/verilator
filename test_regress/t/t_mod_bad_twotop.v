// $Id:$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;
   initial begin
      $write("Two top modules\n");
      $stop;
   end
endmodule

module t2;
   initial begin
      $write("Two top modules\n");
      $stop;
   end
endmodule
