// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

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
      automatic int st = 2; st++; return st;
   endfunction

   function static int f_st_no ();
      int st = 2; st++; return st;
   endfunction
   function static int f_st_st ();
      static int st = 2; st++; return st;
   endfunction
   function static int f_st_au ();
      automatic int st = 2; st++; return st;
   endfunction

   function automatic int f_au_no ();
      int st = 2; st++; return st;
   endfunction
   function automatic int f_au_st ();
      static int st = 2; st++; return st;
   endfunction
   function automatic int f_au_au ();
      automatic int st = 2; st++; return st;
   endfunction

   initial begin
      if (f_no_no() != 3) $stop;
      if (f_no_no() !=   4) $stop;
      if (f_no_st() != 3) $stop;
      if (f_no_st() !=   4) $stop;
      if (f_no_au() != 3) $stop;
      if (f_no_au() !=   3) $stop;
      //
      if (f_st_no() != 3) $stop;
      if (f_st_no() !=   4) $stop;
      if (f_st_st() != 3) $stop;
      if (f_st_st() !=   4) $stop;
      if (f_st_au() != 3) $stop;
      if (f_st_au() !=   3) $stop;
      //
      if (f_au_no() != 3) $stop;
      if (f_au_no() !=   3) $stop;
      if (f_au_st() != 3) $stop;
      if (f_au_st() !=   4) $stop;
      if (f_au_au() != 3) $stop;
      if (f_au_au() !=   3) $stop;
      //
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
