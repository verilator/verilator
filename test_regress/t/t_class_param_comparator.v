// Minimal non-UVM repro.
// base class with type-of-type default overridden by derived class.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

package pkg;

  class builtin_comp #(
      type T = int
  );
    static function bit comp(T a, T b);
      return 1;
    endfunction
  endclass

  class class_comp #(
      type T = int
  );
    static function bit comp(T a, T b);
      return 1;
    endfunction
  endclass

  virtual class comparator #(
      type T = int,
      type comp_type = builtin_comp#(T)
  );
  endclass

  class class_comparator #(
      type T = int
  ) extends comparator #(T, class_comp #(T));
  endclass

endpackage

module t;
  import pkg::*;

  class c;
    int i;
    function bit compare(c rhs);
      return i == rhs.i;
    endfunction
    function void copy(c rhs);
      rhs.i = i;
    endfunction
  endclass

  initial begin
    class_comparator #(c) sb;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
