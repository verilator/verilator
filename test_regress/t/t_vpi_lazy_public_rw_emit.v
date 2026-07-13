// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Unpacked struct/array residual expansion in symbol emitter under --vpi-lazy-public-rw.

module top(input clk, input [7:0] a, output [7:0] o);
   typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;
   typedef struct { logic [7:0] m; logic [7:0] n; } us_t;  // unpacked struct

   us_t us_sig;              // unpacked struct -> residual member expansion
   us_t usarr [0:1];         // unpacked array of struct -> residual expansion
   ps_t psarr [0:1];         // unpacked array of packed struct -> residual

   always_comb begin
      us_sig.m = a;
      us_sig.n = ~a;
      usarr[0].m = a;
      usarr[1].n = ~a;
      psarr[0].hi = a[3:0];
      psarr[1].lo = a[7:4];
   end

   logic [7:0] sub_o;
   sub subi(.o(sub_o), .a(a));

   assign o = us_sig.m ^ usarr[0].m ^ {psarr[0].hi, psarr[1].lo} ^ sub_o;
endmodule

// Non-ANSI split port: the direction and the type are declared separately, so
// AstVar::combineType merges the two declarations (propagating the lazy-VPI
// flag) - exercised under --vpi-lazy-public-rw.
module sub(o, a);
   output o;
   logic [7:0] o;
   input [7:0] a;
   always_comb o = ~a;
endmodule
