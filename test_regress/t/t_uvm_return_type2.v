// DESCRIPTION: Verilator: Verify parameterized class self-referential return
// types work with explicit-range value parameters (e.g. logic [7:0]).
//
// This exposes a gap where the declared type has a Range child not yet folded
// by V3Width, so the targeted keyword-width normalization cannot determine the
// port width.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

  class cls #(logic [7:0] T = 8'd1);
    static function cls#(T) f();
      cls#(T) c = new();
      return c;
    endfunction
  endclass

  initial begin
    static cls#(8'd0) c = cls#(8'd0)::f();
    if (c == null) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
