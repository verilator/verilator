// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface Bus;
  logic [15:0] data;
endinterface

module t_sched_act;
  logic clk = 0;
  integer cyc = 0;
  Bus intf();
  virtual Bus vif = intf;
  logic [15:0] data;

  always @(posedge clk) begin
    cyc <= cyc + 1;
  end

  // Finish on negedge so that $finish is last
  always @(negedge clk)
    if (cyc >= 6) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

  always @(posedge clk or data) begin
    if (cyc == 1) intf.data <= 'hdead;
    else if (cyc == 2) intf.data <= 'hbeef;
    else if (cyc == 3) intf.data <= 'hface;
    else if (cyc == 4) intf.data <= 'hcafe;
  end

  always @(negedge clk) begin
    data <= vif.data;
  end

  always @(data) begin
    $write("[%0t] data==%h\n", $time, data);
  end

  initial begin
    repeat (10) #5ns clk = ~clk;
  end
endmodule
