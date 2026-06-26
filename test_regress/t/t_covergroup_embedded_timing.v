// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Full clocking-event support for embedded covergroups (IEEE 1800-2023 19.8.1):
// with --timing a covergroup is sampled on every occurrence of its clocking event,
// regardless of where the event signal is written.  This exercises events driven
// from OUTSIDE the enclosing class (impossible to model without --timing) and a
// complex member-chain event, both of which the --no-timing path cannot sample.

class ExtClkMonitor;
  bit clk;  // Clocking-event signal driven only from outside the class
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
  bit a;  // First clocking term, driven externally
  Mid mid;  // Second clocking term reached via a member chain, driven externally
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
    chain = new;

    // Drive the clocking event from OUTSIDE the class: 8 external posedges, all
    // sampling the 'hi' range -> cp_value.hi = 8, cp_value.lo = 0.
    for (i = 0; i < 8; ++i) begin
      extm.value = 4'h8 | i[3:0];
      extm.clk = 1'b0;
      #1;
      extm.clk = 1'b1;
      #1;
    end

    // Complex member-chain event: 4 posedges on 'a' (hi range) and 3 posedges on
    // 'mid.lvl.ev' (lo range), all driven externally -> cp_value.hi = 4, .lo = 3.
    for (i = 0; i < 4; ++i) begin
      chain.value = 4'hC;
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
