// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2008 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   // See also t_preproc_kwd.v

   integer bit; initial bit = 1;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
