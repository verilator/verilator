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

   initial begin
      `checkh(f_no_no(), 3);
      `checkh(f_no_no(),   4);
      `checkh(f_no_st(), 3);
      `checkh(f_no_st(),   4);
      `checkh(f_no_au(), 3);
      `checkh(f_no_au(),   3);
      //
      `checkh(f_st_no(), 3);
      `checkh(f_st_no(),   4);
      `checkh(f_st_st(), 3);
      `checkh(f_st_st(),   4);
      `checkh(f_st_au(), 3);
      `checkh(f_st_au(),   3);
      //
      `checkh(f_au_no(), 3);
      `checkh(f_au_no(),   3);
      `checkh(f_au_st(), 3);
      `checkh(f_au_st(),   4);
      `checkh(f_au_au(), 3);
      `checkh(f_au_au(),   3);
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
         `checkh(ist1, 10);
         `checkh(ist2, 20);
         `checkh(iau3, 30);
         ++ist1;
         ++ist2;
         ++iau3;
      end
      else if (cyc == 1) begin
         `checkh(ist1, 11);
         `checkh(ist2, 21);
         `checkh(iau3, 0);
      end
      else if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
