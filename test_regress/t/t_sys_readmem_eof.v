// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define STRINGIFY(x) `"x`"

module t();
   reg [7:0] rom [4];
   initial begin
      $readmemh({`STRINGIFY(`TEST_OBJ_DIR), "/dat.mem"}, rom);
      `checkh(rom[0], 8'h1);
      `checkh(rom[1], 8'h10);
      `checkh(rom[2], 8'h20);
      `checkh(rom[3], 8'h30);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
