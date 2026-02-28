// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

interface sys_if;
  logic clk;
endinterface

interface axi_if;
  wire clk;
endinterface

class sys_config;
  virtual sys_if sys_vi;
endclass

class axi_agent_config;
  virtual axi_if axi_vi;
  sys_config cfg;
  task start_clk();
    fork
      forever begin
        cfg.sys_vi.clk = 1'b1;
        #1;
      end
    join_none
    @(posedge axi_vi.clk);
  endtask
  task test();
    cfg.sys_vi.clk = 0;
    #1;
    start_clk();
    $write("*-* All Finished *-*\n");
    $finish;
  endtask
endclass

module axi_tb_top;
  sys_if sys_vi ();
  axi_if axi_vi ();
  assign axi_vi.clk = sys_vi.clk;
  sys_config a;
  axi_agent_config b;
  initial begin
    a = new;
    b = new;
    a.sys_vi = sys_vi;
    b.axi_vi = axi_vi;
    b.cfg = a;
    b.test();
    #3 $stop;
  end
endmodule
