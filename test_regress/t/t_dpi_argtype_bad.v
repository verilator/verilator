// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2021 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

   typedef struct { string a; string b; } foo_t;

   import "DPI-C" task dpix_twice(foo_t arg);
   initial begin
      $stop;
   end
endmodule
