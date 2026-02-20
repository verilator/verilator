// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   enum bit [1:0] { BADX = 2'b1x } BAD1;

   enum logic [3:0] { e0 = 4'b1xx1,
                      e1
                      } BAD2;

   initial begin
      $stop;
   end

endmodule
