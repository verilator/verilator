// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/);

   import "DPI-C" function void dpii_test();

   initial begin
      $write("*-* All Finished *-*\n");
      dpii_test();  // $finish
   end
endmodule
