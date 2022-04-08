// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

package Pkg;
class Cls;
   int c_no = 2;
   //automatic int c_au = 2;  // automatic not a legal keyword here
   static int c_st = 22;

   function int f_c_no ();
      ++c_no; return c_no;
   endfunction
   function int f_c_st ();
      ++c_st; return c_st;
   endfunction

   static function int f_cs_st ();
      ++c_st; return c_st;
   endfunction

endclass
endpackage

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   Pkg::Cls a = new;
   Pkg::Cls b = new;

   int   v;

   initial begin
      v = a.f_c_no(); `checkh(v, 3);
      v = a.f_c_no(); `checkh(v, 4);
      v = b.f_c_no(); `checkh(v, 3);
      v = b.f_c_no(); `checkh(v, 4);
      v = a.f_c_st(); `checkh(v, 23);
      v = a.f_c_st(); `checkh(v, 24);
      v = b.f_c_st(); `checkh(v, 25);
      v = b.f_c_st(); `checkh(v, 26);
      //
      v = Pkg::Cls::f_cs_st(); `checkh(v, 27);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
