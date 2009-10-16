// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t;
   parameter [ BMSB : BLSB ] B = A[23:20]; // 3
   parameter A = 32'h12345678;
   parameter BLSB = A[16+:4];  // 4
   parameter BMSB = A[7:4]; // 7

   initial begin
      if (B !== 4'h3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
