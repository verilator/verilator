// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t ();

   // Can't handle time (yet?)
   import "DPI-C" dpii_fa_bit = function logic [2:0] oth_f_int1(input time i);

   initial begin
      $stop;
   end

endmodule
