// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/);

   sub #(.P(1)) suba ();
   sub #(.P(10)) subb ();

   int v;

   initial begin
      v = suba.f_no_st(); `checkh(v, 3);
      v = suba.f_no_st(); `checkh(v, 4);
      v = subb.f_no_st(); `checkh(v, 'hc);
      v = subb.f_no_st(); `checkh(v, 'h16);
      v = suba.f_no_st(); `checkh(v, 5);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module sub;
   parameter P = 1;
   function int f_no_st ();
      // This static is unique within each parameterized module
      static int st = 2; st += P; return st;
   endfunction
endmodule
