// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkg(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%g' exp='%g'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/);

   initial begin
      int i;
      string a [string];
      string k;
      string v;

      a = '{ "f": "fooed", "b": "bared", default: "defaulted" };
      i = a.size(); `checkh(i, 2);  // Default doesn't count
      v = a["f"]; `checks(v, "fooed");
      v = a["b"]; `checks(v, "bared");
      v = a["NEXISTS"]; `checks(v, "defaulted");

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
