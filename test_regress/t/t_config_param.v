// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module m1;
   parameter string P1 = "p1.unchanged";
   parameter string P2 = "p2.unchanged";
   initial $display("m1 %%m=%m %%l=%l P1=%s P2=%s", P1, P2);
endmodule

module t;

   m1 u_1a();
   m1 u_1b();
   m1 u_1c();

   final $write("*-* All Finished *-*\n");

endmodule

config cfg1;
   localparam P1 = "cfg.p1";
   localparam P2 = "cfg.p2";
   design t;
   instance t.u_1a use #(.P1(), .P2("override.u_a.p2"));
   instance t.u_1b use #();  // All parameters back to default
   instance t.u_1c use #(.P1(P1), .P2(P2));
endconfig
