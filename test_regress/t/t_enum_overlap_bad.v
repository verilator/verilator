// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   enum { e0,
          e1,
          e2,
          e1b=1
          } BAD1;

   initial begin
      $stop;
   end

endmodule
