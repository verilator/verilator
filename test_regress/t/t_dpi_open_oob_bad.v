// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/);

   import "DPI-C" function void dpii_nullptr();

   // verilator lint_off UNDRIVEN
   int i_int_u3 [2:-2] [-3:3] [4:-4];
   import "DPI-C" function void dpii_int_u3(input int i [] [] []);

   real i_real_u1 [1:0];
   import "DPI-C" function void dpii_real_u1(input real i []);

   bit i_u6 [2][2][2][2][2][2];
   import "DPI-C" function void dpii_bit_u6(input bit i [][][][][][]);

   real i_real_u6 [2][2][2][2][2][2];
   import "DPI-C" function void dpii_real_u6(input real i [][][][][][]);

   initial begin
      i_int_u3[0][0][0] = 32'hbad;
      i_real_u1[0] = 1.1;
      i_u6[0][0][0][0][0][0] = 1'b1;

      dpii_nullptr();
      dpii_int_u3(i_int_u3);
      dpii_real_u1(i_real_u1);
      dpii_bit_u6(i_u6);
      dpii_real_u6(i_real_u6);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
