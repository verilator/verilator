// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkb(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='b%x exp='b%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

class Cls;
   int i;
endclass

module t;
   initial begin
      Cls a = new;
      Cls b = new;
      // Two checks because == and != may not be derived from each other
      `checkb(a != b, 1'b1)
      `checkb(a == b, 1'b0)
      a = b;
      `checkb(a == b, 1'b1)
      `checkb(a != b, 1'b0)
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
