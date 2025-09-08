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
    #1 axi_vi.clk = 1'b1;  // triggers line 26
    #1 axi_vi.clk = 1'b0;  // triggers line 29 (shouldn't happen)
    #1 axi_vi.clk = 1'b1;  // triggers line 18 (shouldn't happen)
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
    axi_vi.cb.rvalid <= 1'b1;  // assigned on first clk posedge (line 13)
    @(posedge axi_vi.rvalid);
    $display("[%0t] rvalid <= 0", $time);
    axi_vi.cb.rvalid <= 1'b0;  // assigned on second clk posedge (line 15), but should be on first
    @(negedge axi_vi.clk);
    $display("[%0t] rlast <= 1", $time);
    axi_vi.cb.rlast <= 1'b1;  // assigned on second clk posedge (line 15), shouldn't happen
  end
endmodule
module t;
  axi_if axi_vi ();
  sub i_sub (axi_vi);
endmodule
