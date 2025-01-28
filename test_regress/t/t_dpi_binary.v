// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t ();

   initial begin
      // All Finished is in dpic_final
      $finish;
   end

   import "DPI-C" context function void dpic_final();
   final dpic_final();

endmodule
