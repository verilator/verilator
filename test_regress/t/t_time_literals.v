// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

`timescale 1ns/1ps

module t;
   time t;

   // realtime value scaled to timeunit, rounded to timeprecision
   initial begin
      // verilator lint_off REALCVT
      t = 1s; `checkd(t, 64'd1000000000);
      t = 2ms; `checkd(t, 2000000);
      t = 1ms; `checkd(t, 1000000);
      t = 1us; `checkd(t, 1000);
      t = 1ns; `checkd(t, 1);
      t = 1ps; `checkd(t, 0);  // Below precision
      t = 1fs; `checkd(t, 0);

      t = 2.3ps; `checkd(t, 0);
      t = 2.4us; `checkd(t, 2400);
      // verilator lint_on REALCVT

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
