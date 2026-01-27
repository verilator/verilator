// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   mailbox #(int) m;

   initial begin
      m = new(4);
      if (m.bad_method() != 0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
