// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   typedef struct {
      int         a;
      int         b;
      byte        c;
   } sabcu_t;

   typedef struct packed {
      int         a;
      int         b;
      byte        c;
   } sabcp_t;

   sabcu_t abcu;
   sabcp_t abcp;

   initial begin
      abcp = '{1, 2, 3};
      abcu = '{1, 2, 3};
      if (abcp.a !== 1) $stop;
      if (abcp.b !== 2) $stop;
      if (abcp.c !== 3) $stop;
      if (abcu.a !== 1) $stop;
      if (abcu.b !== 2) $stop;
      if (abcu.c !== 3) $stop;

      abcp = '{default:4, int:5};
      abcu = '{default:4, int:5};
      if (abcp.a !== 5) $stop;
      if (abcp.b !== 5) $stop;
      if (abcp.c !== 4) $stop;
      if (abcu.a !== 5) $stop;
      if (abcu.b !== 5) $stop;
      if (abcu.c !== 4) $stop;

      abcp = '{int:6, byte:7, int:8};
      abcu = '{int:6, byte:7, int:8};
      if (abcp.a !== 8) $stop;
      if (abcp.b !== 8) $stop;
      if (abcp.c !== 7) $stop;
      if (abcu.a !== 8) $stop;
      if (abcu.b !== 8) $stop;
      if (abcu.c !== 7) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
