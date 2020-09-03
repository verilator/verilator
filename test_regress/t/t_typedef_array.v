// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by James Pallister.
// SPDX-License-Identifier: CC0-1.0

typedef logic logic_alias_t;

module t;
   logic_alias_t [6:1] signal;
   // verilator lint_off LITENDIAN
   logic_alias_t [1:6] signal2;
   // verilator lint_on LITENDIAN

   initial begin
      signal[6:1] = 'b100001;
      signal[3] = 'b1;
      signal2[1:6] = 'b100001;
      signal2[4] = 'b1;

      if (signal != 'b100101) $stop;
      if (signal2 != 'b100101) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
