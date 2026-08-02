// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class ExtClkMonitor;
  bit clk;
  bit [3:0] value;

  covergroup ext_cg @(posedge clk);
    cp_val: coverpoint value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
  endgroup

  function new();
    ext_cg = new;
  endfunction
endclass

class Lvl;
  bit ev;
endclass

class Mid;
  Lvl lvl;
endclass

class ChainMonitor;
  bit a;
  Mid mid;
  bit [3:0] value;

  covergroup chain_cg @(posedge a or posedge mid.lvl.ev);
    cp_val: coverpoint value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
  endgroup

  function new();
    mid = new;
    mid.lvl = new;
    chain_cg = new;
  endfunction
endclass

module t;
  ExtClkMonitor extm;
  ChainMonitor chain;
  int i;

  initial begin
    extm = new;
    extm.value = 4'h3;
    // This edge must be sampled before the caller first blocks at #1 (IEEE 1800-2023 19.3);
    // normal fork-join_none startup deferral (IEEE 1800-2023 9.3.2) would miss it.
    extm.clk = 1'b1;
    #1;
    chain = new;

    for (i = 0; i < 8; ++i) begin
      extm.value = 4'h8 | i[3:0];
      extm.clk = 1'b0;
      #1;
      extm.clk = 1'b1;
      #1;
    end

    for (i = 0; i < 4; ++i) begin
      chain.value = 4'hc;
      chain.a = 1'b0;
      #1;
      chain.a = 1'b1;
      #1;
    end
    for (i = 0; i < 3; ++i) begin
      chain.value = 4'h2;
      chain.mid.lvl.ev = 1'b0;
      #1;
      chain.mid.lvl.ev = 1'b1;
      #1;
    end

    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
