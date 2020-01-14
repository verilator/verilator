// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.

module t;

   reg [5:0] assoc_bad_key[real];
   real assoc_bad_value[int];

   initial begin
      $readmemb("not", assoc_bad_key);
      $readmemb("not", assoc_bad_value);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
