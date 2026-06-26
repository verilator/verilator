// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class msg;
  string context_name;

  function void set_context(string name);
    context_name = name;
  endfunction
endclass

package helper_pkg;
  int package_counter;

  function void bump();
    package_counter++;
  endfunction
endpackage

interface intf(output logic a, output logic b);
  msg m;
  event e;

  task go();
    helper_pkg::package_counter++;
    go_helper();
    go_helper();
  endtask

  task go_helper();
    // verilator no_inline_task
    m.set_context("go_helper");
    helper_pkg::bump();
    -> e;
    a <= 1;
  endtask
endinterface

class driver;
  virtual intf vif;

  function new(virtual intf vif);
    this.vif = vif;
  endfunction

  task go();
    vif.go();
  endtask
endclass

module t;
  wire a;
  wire b;
  virtual intf vif;

  intf i(a, b);

  initial begin
    driver d;
    vif = t.i;
    t.i.m = new;
    d = new(t.i);
    d.go();
  end

  always @(posedge a) begin
    vif.b <= 1;
  end

  always @(*) begin
    if (a && b) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
