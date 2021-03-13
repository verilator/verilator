// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef verilator
 `define stop $stop
`else
 `define stop
`endif
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class Cls;
   bit b;
   int i;
   bit [15:0] carray4 [4];
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c = new;
      c.b = '1;
      c.i = 42;
      $display("'%p'", c);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
