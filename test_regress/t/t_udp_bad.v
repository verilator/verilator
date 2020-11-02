// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   wire a, b;
   udp_x x (a, b);

endmodule

primitive udp_x (a_bad, b, c_bad);
   tri  a_bad;
   output b;
   output c_bad;
   table
      //a   b
      0  :   1;
      1  :   0;
   endtable
endprimitive
