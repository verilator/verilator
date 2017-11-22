// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t (/*AUTOARG*/);

   if (0) begin
      $warning("User compile-time warning");
      $error("User compile-time error");
   end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
