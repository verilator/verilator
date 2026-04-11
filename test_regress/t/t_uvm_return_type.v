// DESCRIPTION: Verilator: Verify that a parameterized class's static function
// return type resolves to the same specialization as the caller's context.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

  class cls #(bit T = 1);
    static function cls#(T) f();
      cls#(T) c = new();
      return c;
    endfunction
  endclass

  initial begin
    static cls#(0) c = cls#(0)::f();
    if (c == null) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
