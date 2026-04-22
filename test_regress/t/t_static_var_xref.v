// DESCRIPTION: Verilator: Dotted reference that uses another dotted reference
// as the select expression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package test_pkg;
  class foo;
    virtual function void visit();
      static int compiled_regex;
      compiled_regex = 1;
      endfunction

      function void end_v();
        visit.compiled_regex = 0;
      endfunction
    endclass
endpackage

module t;
  initial begin
    $write("*-* All Coverage Tests Passed *-*\n");
    $finish;
  end
endmodule

