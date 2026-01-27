// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2023 Don Williamson and Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module top;
   string scope;
   initial begin
      scope = $sformatf("%m");
      $write("[%0t] In %s\n", $time, scope);
      `ifdef MAIN_TOP_NAME_EMPTY
         if (scope != "top") $stop;
      `else
         if (scope != "ALTOP.top") $stop;
      `endif
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
