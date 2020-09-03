// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   reg signed [20:0] longp;
   reg signed [20:0] longn;
   reg signed [40:0] quadp;
   reg signed [40:0] quadn;
   reg signed [80:0] widep;
   reg signed [80:0] widen;

   initial begin
      longp = 21'shbbccc;
      longn = 21'shbbccc; longn[20] = 1'b1;
      quadp = 41'sh1_bbbb_cccc;
      quadn = 41'sh1_bbbb_cccc; quadn[40] = 1'b1;
      widep = 81'shbc_1234_5678_1234_5678;
      widen = 81'shbc_1234_5678_1234_5678; widen[40] = 1'b1;

      // Display formatting
      $display("[%0t] lp %%x=%x %%x=%x %%o=%o %%b=%b %%0d=%0d %%d=%d %%p=%p %%0p=%0p",
               $time, longp, longp, longp, longp, longp, longp, longp, longp);
      $display("[%0t] ln %%x=%x %%x=%x %%o=%o %%b=%b %%0d=%0d %%d=%d %%p=%p %%0p=%0p",
               $time, longn, longn, longn, longn, longn, longn, longn, longn);
      $display("[%0t] qp %%x=%x %%x=%x %%o=%o %%b=%b %%0d=%0d %%d=%d %%p=%p %%0p=%0p",
               $time, quadp, quadp, quadp, quadp, quadp, quadp, quadp, quadp);
      $display("[%0t] qn %%x=%x %%x=%x %%o=%o %%b=%b %%0d=%0d %%d=%d %%p=%p %%0p=%0p",
               $time, quadn, quadn, quadn, quadn, quadn, quadn, quadn, quadn);
      $display("[%0t] wp %%x=%x %%x=%x %%o=%o %%b=%b %%p=%p %%0p=%0p",
               $time, widep, widep, widep, widep, widep, widep);
      $display("[%0t] wn %%x=%x %%x=%x %%o=%o %%b=%b %%p=%p %%0p=%0p",
               $time, widen, widen, widen, widen, widen, widen);
      $display;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
