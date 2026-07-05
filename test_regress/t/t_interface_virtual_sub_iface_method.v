// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface inner_if;
  logic [7:0] cnt = 0;
  function automatic void bump();
    cnt = cnt + 1;
  endfunction
  function automatic logic [7:0] get();
    return cnt;
  endfunction
  task automatic addn(input logic [7:0] n);
    cnt = cnt + n;
  endtask
endinterface

interface mid_if;
  inner_if sub ();
endinterface

interface data_if;
  logic [7:0] val = 0;
endinterface

interface outer_if;
  inner_if a ();
  inner_if b ();
  mid_if m ();
  data_if d ();
endinterface

class driver_c;
  virtual outer_if vif;
  task run();
    vif.a.bump();  // sibling a: void function, +1
    vif.b.bump();  // sibling b: void function, +1
    vif.b.addn(8'd5);  // sibling b: task with arg, +5
    vif.m.sub.bump();  // two-level nesting, +1
    vif.d.val = 8'd99;  // sub-interface variable write via vif (no method)
  endtask
  function logic [7:0] read_a();
    return vif.a.get();  // function returning value via vif sub-interface
  endfunction
endclass

module t;
  outer_if oif ();
  driver_c drv;
  initial begin
    drv = new();
    drv.vif = oif;
    drv.run();
    // Per-instance dispatch: a, b and m.sub are distinct instances.
    `checkd(oif.a.cnt, 8'd1)
    `checkd(oif.b.cnt, 8'd6)
    `checkd(oif.m.sub.cnt, 8'd1)
    `checkd(drv.read_a(), 8'd1)
    `checkd(oif.d.val, 8'd99)
    // Direct (non-virtual) sub-interface method call: covers the non-virtual dtype path.
    oif.a.bump();
    `checkd(oif.a.cnt, 8'd2)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
