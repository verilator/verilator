// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;

   reg [175:0] hex [15:0];

   integer   i;

   initial begin
      $readmemh("t/t_sys_readmem_bad_end.mem", hex, 0, 15);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
