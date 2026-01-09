// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface axi_if;
  logic clk;
  wire rlast;
  wire rvalid;
  clocking cb @(posedge clk);
    inout rlast, rvalid;
  endclocking
  modport md1(clocking cb, inout clk, rlast, rvalid);
  modport md2(clocking cb);
endinterface

module sub (
    axi_if.md1 axi1,
    axi_if.md2 axi2
);
  initial begin
    axi1.clk = 1'b0;
    #1 axi1.clk = 1'b1;
    #1 axi1.clk = 1'b0;
    #1 axi1.clk = 1'b1;
  end
  initial begin
    @(negedge axi1.rvalid);
    $display("[%0t] rvalid==%b", $time, axi1.rvalid);
    $display("[%0t] rlast is 1: ", $time, axi1.rlast === 1);
    if (axi1.rlast === 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
  initial begin
    $display("[%0t] rvalid <= 1", $time);
    axi1.cb.rvalid <= 1'b1;
    @(posedge axi1.rvalid);
    $display("[%0t] rvalid <= 0", $time);
    axi1.cb.rvalid <= 1'b0;
    @(negedge axi1.clk);
    $display("[%0t] rlast <= 1", $time);
    axi2.cb.rlast <= 1'b1;
  end
endmodule

module t;
  axi_if axi_vi ();
  sub i_sub (
      .axi1(axi_vi),
      .axi2(axi_vi)
  );
endmodule
