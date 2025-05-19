// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t ();

`ifndef VERILATOR
   `error "Only Verilator supports PLI-ish DPI calls and sformat conversion."
`endif

   import "DPI-C" context dpii_display_call
     = function void \$dpii_display
       (input string formatted /*verilator sformat*/, input string other_bad );

   initial begin
      $dpii_display("hello", "huh");
      $stop;
   end

endmodule
