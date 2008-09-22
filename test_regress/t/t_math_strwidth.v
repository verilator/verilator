// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008-2008 by Wilson Snyder.

module t (/*AUTOARG*/);

   reg [4*8:1] strg;

   initial begin
      strg = "CHK";
      if (strg != "CHK") $stop;
      if (strg == "JOE") $stop;
      $write("String = %s = %x\n", strg, strg);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
