// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

   // bug1081 - We don't use VPI, just need SC with VPI

   initial begin
      $write("%0t: Hello\n", $time);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule : t
