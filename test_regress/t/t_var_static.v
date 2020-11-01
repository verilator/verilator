// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   function int f_no_no ();
      int st = 2; st++; return st;
   endfunction
   function int f_no_st ();
      static int st = 2; st++; return st;
   endfunction
   function int f_no_au ();
      automatic int au = 2; au++; return au;
   endfunction

   function static int f_st_no ();
      int st = 2; st++; return st;
   endfunction
   function static int f_st_st ();
      static int st = 2; st++; return st;
   endfunction
   function static int f_st_au ();
      automatic int au = 2; au++; return au;
   endfunction

   function automatic int f_au_no ();
      int au = 2; au++; return au;
   endfunction
   function automatic int f_au_st ();
      static int st = 2; st++; return st;
   endfunction
   function automatic int f_au_au ();
      automatic int au = 2; au++; return au;
   endfunction

   int v;

   initial begin
      v = f_no_no(); `checkh(v, 3);
      v = f_no_no(); `checkh(v,   4);
      v = f_no_st(); `checkh(v, 3);
      v = f_no_st(); `checkh(v,   4);
      v = f_no_au(); `checkh(v, 3);
      v = f_no_au(); `checkh(v,   3);
      //
      v = f_st_no(); `checkh(v, 3);
      v = f_st_no(); `checkh(v,   4);
      v = f_st_st(); `checkh(v, 3);
      v = f_st_st(); `checkh(v,   4);
      v = f_st_au(); `checkh(v, 3);
      v = f_st_au(); `checkh(v,   3);
      //
      v = f_au_no(); `checkh(v, 3);
      v = f_au_no(); `checkh(v,   3);
      v = f_au_st(); `checkh(v, 3);
      v = f_au_st(); `checkh(v,   4);
      v = f_au_au(); `checkh(v, 3);
      v = f_au_au(); `checkh(v,   3);
      //
   end

   int cyc = 0;
   always @ (posedge clk) begin
      int ist1;
      static int ist2;
      automatic int iau3;

      cyc <= cyc + 1;
      if (cyc == 0) begin
         ist1 = 10;
         ist2 = 20;
         iau3 = 30;
         v = ist1; `checkh(v, 10);
         v = ist2; `checkh(v, 20);
         v = iau3; `checkh(v, 30);
         ++ist1;
         ++ist2;
         ++iau3;
      end
      else if (cyc == 1) begin
         v = ist1; `checkh(v, 11);
         v = ist2; `checkh(v, 21);
         //TODO v = iau3; `checkh(v, 0);
      end
      else if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
