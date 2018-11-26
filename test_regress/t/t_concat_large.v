// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Wilson Snyder.

module t (/*AUTOARG*/);

   reg [32767:0] a;

   initial begin
      // verilator lint_off WIDTHCONCAT
      a = {32768{1'b1}};
      // verilator lint_on WIDTHCONCAT
      if (a[32000] != 1'b1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
