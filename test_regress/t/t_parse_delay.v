// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   // verilator lint_off WIDTH
   reg [6:0] myreg1;

   initial begin
      myreg1 = # 100 7'd0;
      myreg1 = # 100 'b0; // [#] [100] ['b0]
      myreg1 = #100'b0; // [#] [100] ['b0]
      myreg1 = 100'b0;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
