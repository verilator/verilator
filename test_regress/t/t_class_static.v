// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

class Cls;
   int c_no = 2;
   //automatic int c_au = 2;  // automatic not a legal keyword here
   static int c_st = 2;

   function int f_c_no ();
      ++c_no; return c_no;
   endfunction
   function int f_c_st ();
      ++c_st; return c_st;
   endfunction

   function int f_no_no ();
      int au = 2; au++; return au;
   endfunction
   function int f_no_st ();
      static int st = 2; st++; return st;
   endfunction
   function int f_no_au ();
      automatic int au = 2; au++; return au;
   endfunction
endclass

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   Cls a = new;
   Cls b = new;

   int   v;

   initial begin
      v = a.f_c_no(); `checkh(v,3);
      v = a.f_c_no(); `checkh(v,  4);
      v = b.f_c_no(); `checkh(v,  3);
      v = b.f_c_no(); `checkh(v,  4);
      v = a.f_c_st(); `checkh(v,3);
      v = a.f_c_st(); `checkh(v,  4);
      v = b.f_c_st(); `checkh(v,  5);
      v = b.f_c_st(); `checkh(v,  6);
      //
      v = a.f_no_no(); `checkh(v, 3);
      v = a.f_no_no(); `checkh(v,   3);
      v = b.f_no_no(); `checkh(v,   3);
      v = b.f_no_no(); `checkh(v,   3);
      v = a.f_no_st(); `checkh(v, 3);
      v = a.f_no_st(); `checkh(v,   4);
      v = b.f_no_st(); `checkh(v,   5);
      v = b.f_no_st(); `checkh(v,   6);
      v = a.f_no_au(); `checkh(v, 3);
      v = a.f_no_au(); `checkh(v,   3);
      v = b.f_no_au(); `checkh(v,   3);
      v = b.f_no_au(); `checkh(v,   3);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
