// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   sub sub();
   initial begin
      $write("t: ");
      $printtimescale;
      sub.pts();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

`timescale 1s/1s
module sub;
   task pts;
      $write("sub: ");
      $printtimescale;
   endtask
endmodule
