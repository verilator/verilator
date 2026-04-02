// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

interface my_if;
  logic clk = 0;
  bit   clk_active = 0;

  initial begin
    wait (clk_active);
    forever #5 clk = ~clk;
  end

  function void start_clk();
    clk_active = 1;
  endfunction
endinterface

class Driver;
  virtual my_if vif;
  task run();
    #10;
    vif.start_clk();
  endtask
endclass

module t;
  my_if intf();
  my_if intf_unused();  // Second instance triggered the bug

  initial begin
    automatic Driver d = new;
    d.vif = intf;
    d.run();
    repeat (4) @(posedge intf.clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
