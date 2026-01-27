// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

   export "DPI-C" task dpix_twice;
   export "DPI-C" dpix_t_int_renamed = task dpix_twice;
   task dpix_twice(input int i, output int o);  o = ~i; endtask

   initial begin
      $stop;
   end
endmodule
