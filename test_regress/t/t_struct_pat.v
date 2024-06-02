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

   typedef struct {
      int         a;
      int         b4[4];
   } sab4u_t;

   typedef struct packed {
      int         a;
      bit [3:0][31:0] b4;
   } sab4p_t;

   sab4u_t ab4u[2][3];
   sab4p_t ab4p[2][3];

   initial begin
      abcp = '{1, 2, 3};
      abcu = '{1, 2, 3};
      if (abcp.a !== 1) $stop;
      if (abcp.b !== 2) $stop;
      if (abcp.c !== 3) $stop;
      if (abcu.a !== 1) $stop;
      if (abcu.b !== 2) $stop;
      if (abcu.c !== 3) $stop;

      abcp = '{3{40}};
      abcu = '{3{40}};
      if (abcp.a !== 40) $stop;
      if (abcp.b !== 40) $stop;
      if (abcp.c !== 40) $stop;
      if (abcu.a !== 40) $stop;
      if (abcu.b !== 40) $stop;
      if (abcu.c !== 40) $stop;

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

      ab4p = '{2{'{3{'{10, '{2{20, 30}}}}}}};
      ab4u = '{2{'{3{'{10, '{2{20, 30}}}}}}};
      $display("%p", ab4p);
      if (ab4p[0][0].a !== 10) $stop;
      if (ab4p[0][0].b4[0] !== 30) $stop;
      if (ab4p[0][0].b4[1] !== 20) $stop;
      if (ab4p[0][0].b4[2] !== 30) $stop;
      if (ab4p[0][0].b4[3] !== 20) $stop;
      if (ab4p[1][2].a !== 10) $stop;
      if (ab4p[1][2].b4[0] !== 30) $stop;
      if (ab4p[1][2].b4[1] !== 20) $stop;
      if (ab4p[1][2].b4[2] !== 30) $stop;
      if (ab4p[1][2].b4[3] !== 20) $stop;
      $display("%p", ab4u);
      if (ab4u[0][0].a !== 10) $stop;
      if (ab4u[0][0].b4[0] !== 20) $stop;
      if (ab4u[0][0].b4[1] !== 30) $stop;
      if (ab4u[0][0].b4[2] !== 20) $stop;
      if (ab4u[0][0].b4[3] !== 30) $stop;
      if (ab4u[1][2].a !== 10) $stop;
      if (ab4u[1][2].b4[0] !== 20) $stop;
      if (ab4u[1][2].b4[1] !== 30) $stop;
      if (ab4u[1][2].b4[2] !== 20) $stop;
      if (ab4u[1][2].b4[3] !== 30) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
