// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t (/*AUTOARG*/);

   if (1) begin
      $warning("User compile-time warning");
      $error("User compile-time error");
   end

endmodule
