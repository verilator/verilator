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

// Static formal arguments retain storage after a subroutine call.
module t;
  task st(input int si, inout int sio, output int so);
    sio = sio + si;
    so = si + 1;
  endtask

  function int sf(input int fi);
    return fi * 2;
  endfunction

  task automatic at(input int ai);
    static int as;
    as = ai;
  endtask

  initial begin
    int io;
    int o;
    for (int i = 1; i <= 3; ++i) begin
      io = i * 10;
      st(i, io, o);
      `checkd(io, i * 11);
      `checkd(o, i + 1);
      `checkd(st.si, i);
      `checkd(st.sio, i * 11);
      `checkd(st.so, i + 1);
      `checkd(sf(i), i * 2);
      `checkd(sf.fi, i);
      at(i);
      `checkd(at.as, i);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
