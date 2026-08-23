// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Embedded covergroup events that cannot be approximated without --timing must
// emit COVERIGN rather than silently producing zero coverage.

interface EventIf;
  logic clk;
endinterface

module t;
  EventIf event_if();

  logic ref_clock;
  logic [1:0] ref_clocks;
  virtual EventIf event_vif = event_if;

  class ExternalClk;
    bit clk;
    bit [3:0] value;

    covergroup cov_extclk @(posedge clk);
      coverpoint value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    endgroup

    function new();
      cov_extclk = new;
    endfunction
  endclass

  class Lvl;
    bit ev;
  endclass

  class Mid;
    Lvl lvl;
  endclass

  class ComplexEvt;
    bit a;
    Mid mid;
    bit [3:0] value;

    covergroup cov_cplx @(posedge a or posedge mid.lvl.ev);
      coverpoint value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    endgroup

    function new();
      mid = new;
      mid.lvl = new;
      cov_cplx = new;
    endfunction
  endclass

  class StaticClk;
    static bit clk;
    static bit value;
  endclass

  covergroup cov_static @(posedge StaticClk::clk);
    coverpoint StaticClk::value;
  endgroup

  covergroup cov_ref(ref logic event_ref) @(posedge event_ref);
    coverpoint event_ref;
  endgroup

  covergroup cov_ref_select(ref logic [1:0] event_refs) @(posedge event_refs[0]);
    coverpoint event_refs[0];
  endgroup

  covergroup cov_ref_vif(ref virtual EventIf event_ref_vif) @(posedge event_ref_vif.clk);
    coverpoint event_ref_vif.clk;
  endgroup

  ExternalClk ec;
  ComplexEvt cx;
  cov_static static_cg = new;
  cov_ref ref_cg = new(ref_clock);
  cov_ref_select ref_select_cg = new(ref_clocks);
  cov_ref_vif ref_vif_cg = new(event_vif);

  initial begin
    ec = new;
    cx = new;
    StaticClk::value = 1;
    StaticClk::clk = 1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
