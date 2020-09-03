// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t ();

   // Same name w/ different args
   import "DPI-C" dpii_fa_bit =  function int oth_f_int1(input int i);
   import "DPI-C" pure dpii_fa_bit = function int oth_f_int2(input int i, input int bad);

   initial begin
      $stop;
   end

endmodule
