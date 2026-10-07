// DESCRIPTION: Verilator: Name of a virtual interface in an unnamed model
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc;
endinterface

class Cls;
  virtual ifc vi;
endclass

module t;
  ifc i ();
  initial begin
    Cls c;
    c = new;
    c.vi = i;
    `checks($sformatf("%p", c), "'{vi:t.i}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
