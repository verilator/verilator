// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class Assoc;
  rand int unsigned m[int];
  rand int unsigned s;
  function new;
    m[123] = 1;
    m[456] = 1;
  endfunction
  constraint c {
    solve m before s;
    m[123] == 2;
    m[456] == 3;
    s == 1;
  }
endclass

class Assoc2;
  rand int unsigned m[string];
  rand int unsigned s;
  function new;
    m["abc"] = 1;
    m["def"] = 1;
  endfunction
  constraint c {
    solve m before s;
    m["abc"] == 2;
    m["def"] == 3;
    s == 1;
  }
endclass

module t;
  Assoc o;
  Assoc2 o2;
  initial begin
    o = new;
    o2 = new;
    void'(o.randomize());
    `checkd(o.m[123], 2);
    `checkd(o.m[456], 3);
    `checkd(o.s, 1);

    void'(o2.randomize());
    `checkd(o2.m["abc"], 2);
    `checkd(o2.m["def"], 3);
    `checkd(o2.s, 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
