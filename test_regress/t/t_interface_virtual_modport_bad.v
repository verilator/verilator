// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface Sub;
  logic s;
endinterface

interface Ifc;
  parameter int P = 3;
  logic clk;
  logic a;
  logic b;
  Sub sub ();
  clocking cb @(posedge clk);
    input a;
  endclocking
  clocking cb_not_listed @(posedge clk);
    input a;
  endclocking
  task listed();
  endtask
  task not_listed();
  endtask
  function int not_listed_func();
    return 1;
  endfunction
  modport mp(input a, import listed, export task exp_listed(), clocking cb);
  modport impl(export task exp_unlisted());
endinterface

class Cls;
  virtual Ifc.mp vif;
  int x;
  logic y;
  task run();
    vif.listed();
    vif.exp_listed();
    y = vif.a;
    x = vif.P;
    y = vif.sub.s;
    @(vif.cb);
    vif.not_listed();  // Bad
    vif.exp_unlisted();  // Bad
    vif.b = 1;  // Bad
    x = vif.not_listed_func();  // Bad
    @(vif.cb_not_listed);  // Bad
  endtask
endclass

module impl_m (
    Ifc.mp ie_listed,
    Ifc.impl ie_unlisted
);
  task ie_listed.exp_listed();
  endtask
  task ie_unlisted.exp_unlisted();
  endtask
endmodule

module t;
  Ifc ifc ();
  impl_m m (
      .ie_listed(ifc.mp),
      .ie_unlisted(ifc.impl)
  );
  Cls c;
  initial begin
    c = new;
    c.vif = ifc.mp;
    c.run();
  end
endmodule
