// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   m10 u_10();
   m20 u_20();
   m21 u_21();
   m22 u_22();
   m23 u_23();
   m24 u_24();
   m30 u_30();
   m31 u_31();
   m32 u_32();
   m40 u_40();
   m41 u_41();
   m42 u_42();
   m43 u_43();
   final $write("*-* All Finished *-*\n");
endmodule

config cfg;
   design t;

   // Test uses m10
   default liblist;  // Ignored
   default liblist liba libb;

   // Test uses m20-29
   instance t.m20 liblist;  // Use parent's cell library
   instance t.m21 liblist libc;
   instance t.m22 liblist libc libd;  // m22 in libc
   instance t.m23 liblist libc libd;  // m23 in libd
   instance t.m24 liblist libc libd;  // m24 in default (libb)

   // Test uses m30-39
   instance t.m30 use cell_identifier;
   instance t.m31 use lib_id.cell_id;
   instance t.m32 use #();

   // Test uses m40-49
   cell m40 liblist libc libd;
   cell work.m41 liblist libc libd;
   cell m42 use m42alt;
   cell work.m43 use work.m43alt;

endconfig
