// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Yutetsu TAKATSUKASA. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

   logic [2:0] sig0[3];
   logic [2:0] sig1[3][2];
   bit [2:0]   sig2[3][3];

   import "DPI-C" function void import_func0(input logic [3:0] in [0:2]);
   import "DPI-C" function void import_func1(input logic [2:0] in [0:2]);
   import "DPI-C" function void import_func2(input logic [2:0] in [0:2][0:2]);

   initial begin
      // packed width differs
      import_func0(sig0);
      // dimension differs
      import_func1(sig1);
      // unpacked extent differs
      import_func2(sig1);
      // bit v.s. logic mismatch
      import_func2(sig2);
      // packed var for unpacked port
      import_func0(sig0[1]);
   end
endmodule
