// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;

   reg [175:0] hex [15:0];

   initial begin
      $readmemb("t/t_sys_readmem_bad_digit.mem", hex);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
