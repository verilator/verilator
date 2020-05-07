// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jonathon Donaldson.
// SPDX-License-Identifier: CC0-1.0

// bug855
module our;

   typedef enum logic {n,N} T_Flg_N;

   typedef struct packed {
      T_Flg_N N;
   } T_PS_Reg;

   T_PS_Reg PS = 1'b1;

   initial begin
      $write ("P:%s\n", PS.N.name);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
