// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

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
