// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   integer a, b;

   initial begin
      for (; ; ) ;
      for (; ; a=a+1) ;
      for (; ; a=a+1, b=b+1) ;
      for (; a<1; ) ;
      for (; a<1; a=a+1) ;
      for (; a<1; a=a+1, b=b+1) ;
      for (a=0; a<1; ) ;
      for (a=0; a<1; a=a+1) ;
      for (a=0; a<1; a=a+1, b=b+1) ;
      for (integer a=0; a<1; ) ;
      for (integer a=0; a<1; a=a+1) ;
      for (integer a=0; a<1; a=a+1, b=b+1) ;
      for (var integer a=0; a<1; ) ;
      for (var integer a=0; a<1; a=a+1) ;
      for (var integer a=0; a<1; a=a+1, b=b+1) ;
      for (integer a=0, integer b=0; a<1; ) ;
      for (integer a=0, integer b=0; a<1; a=a+1) ;
      for (integer a=0, integer b=0; a<1; a=a+1, b=b+1) ;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
