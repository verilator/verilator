// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface axi_if;
  logic clk;
  wire  rlast;
  wire  rvalid;
  clocking cb @(posedge clk);
    inout rlast, rvalid;
  endclocking
  modport mcb(clocking cb, inout clk, rlast, rvalid);
endinterface

module sub (
    axi_if.mcb axi_vi
);
  initial begin
    axi_vi.clk = 1'b0;
    #1 axi_vi.clk = 1'b1;
    #1 axi_vi.clk = 1'b0;
    #1 axi_vi.clk = 1'b1;
  end
  initial begin
    @(negedge axi_vi.rvalid);
    $display("[%0t] rvalid==%b", $time, axi_vi.rvalid);
    $display("[%0t] rlast is 1: ", $time, axi_vi.rlast === 1);
    if (axi_vi.rlast === 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
  initial begin
    $display("[%0t] rvalid <= 1", $time);
    axi_vi.cb.rvalid <= 1'b1;
    @(posedge axi_vi.rvalid);
    $display("[%0t] rvalid <= 0", $time);
    axi_vi.cb.rvalid <= 1'b0;
    @(negedge axi_vi.clk);
    $display("[%0t] rlast <= 1", $time);
    axi_vi.cb.rlast <= 1'b1;
  end
endmodule

module t;
  axi_if axi_vi ();
  sub i_sub (axi_vi);
endmodule
