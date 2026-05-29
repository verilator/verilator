// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface intf(output logic a);
  task go();
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

  intf i(a);

  initial begin
    driver d;
    d = new(t.i);
    d.go();
  end

  always @(*) begin
    if (a) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
