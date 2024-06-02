// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;

   timeunit 1ns;
   timeprecision 1ps;

   initial begin
      `checkd($timeunit, -9);
      `checkd($timeunit(), -9);
      `checkd($timeunit(t), -9);

      `checkd($timeprecision, -12);
      `checkd($timeprecision(), -12);
      `checkd($timeprecision(t), -12);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
