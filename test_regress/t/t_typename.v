// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t(/*AUTOARG*/);

   real r;
   logic l;
   typedef bit mybit_t;
   mybit_t [2:0] bitp20;
   mybit_t bitu32 [3:2];
   mybit_t bitu31 [3:1][4:5];

   initial begin
      `checks($typename(real), "real");
      `checks($typename(bit), "bit");
      `checks($typename(int), "int");
      `checks($typename(logic), "logic");
      `checks($typename(string), "string");

      `checks($typename(r), "real");
      `checks($typename(l), "logic");
      `checks($typename(mybit_t), "bit");
      `checks($typename(bitp20), "bit[2:0]");
      `checks($typename(bitu32), "bit$[3:2]");
      `checks($typename(bitu31), "bit$[3:1][4:5]");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
