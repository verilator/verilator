// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import "DPI-C" pure function void dpii_a_library();
import "DPI-C" pure function void dpii_c_library();
import "DPI-C" pure function void dpii_so_library();

module t ();
   initial begin
      dpii_a_library();  // From .a file
      dpii_c_library();  // From .cpp file
      dpii_so_library();  // From .so file
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
