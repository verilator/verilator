// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/);
   int a = 123;
   int b = 321;
   int out;

   import "DPI-C" function void dpii_add
     (int a, int b, ref int out);
   import "DPI-C" function int dpii_add_check
     (int actual, int expected);

   initial begin
      dpii_add(a, b, out);
      if (dpii_add_check(out, (a + b)) != 1) begin
         $write("%%Error: Failure in DPI tests\n");
         $stop;
      end
      else begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
