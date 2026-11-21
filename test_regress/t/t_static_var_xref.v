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

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Static variables in an automatic task retain storage after a call.
module t;
  task automatic at(input int ai);
    static int as;
    as = ai;
  endtask

  initial begin
    for (int i = 1; i <= 3; ++i) begin
      at(i);
      `checkd(at.as, i);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
