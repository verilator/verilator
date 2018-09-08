// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Wilson Snyder.

module t (/*AUTOARG*/);

   localparam string SVEC [0:7] = '{"zero", "one", "two", "three", "four", "five", "six", "seven"};

   initial begin
      $display("%s", SVEC[3'd1]);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
