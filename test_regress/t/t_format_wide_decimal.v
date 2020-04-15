// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t_format_wide_decimal;

   initial begin
      // Format very wide constant number (which has more bits than can
      // be counted in exponent of a double precision float), with %d.
      $display("%d", 1024'hffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
