// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [3:0] foo [1:0];
   initial begin
      foo[0] = 4'b0101;
      foo[1] = 4'b0011;

      `checkh(foo.or, 4'b0111);
      `checkh(foo.and, 4'b0001);
      `checkh(foo.xor, 4'b0110);
      `checkh(foo.sum, 4'b1000);
      `checkh(foo.product, 4'b1111);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
