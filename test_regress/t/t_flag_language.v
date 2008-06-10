// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/);

   // See also t_preproc_kwd.v

   integer bit; initial bit = 1;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
