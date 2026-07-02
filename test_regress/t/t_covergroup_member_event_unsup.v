// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Embedded covergroups (IEEE 1800-2023 19.4) whose clocking event or coverage
// constructs reference enclosing-class members in ways Verilator cannot fully
// support.  Each must emit a clean COVERIGN warning rather than silently
// producing wrong coverage or uncompilable C++.

module t;
  // Coverpoint references an enclosing member, but the covergroup is never
  // constructed (no 'new'), so it cannot be lowered through a back-pointer.
  class NoConstruct;
    bit [3:0] m_x;
    bit m_z;
    covergroup cov_nonew @m_z;
      coverpoint m_x {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    endgroup
  endclass

  // Clocking event on a member that is never assigned inside the class, so no
  // in-class sampling point exists (e.g. the signal is driven only externally).
  class ExternalClk;
    bit clk;
    bit [3:0] m_x;
    covergroup cov_extclk @(posedge clk);
      coverpoint m_x {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    endgroup
    function new();
      cov_extclk = new;
    endfunction
  endclass

  // Clocking event mixing a member signal with a complex member chain that the
  // member-event lowering cannot represent.
  class Lvl;
    bit ev;
  endclass
  class Mid;
    Lvl lvl;
  endclass
  class ComplexEvt;
    bit a;
    Mid mid;
    bit [3:0] m_x;
    covergroup cov_cplx @(posedge a or posedge mid.lvl.ev);
      coverpoint m_x {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    endgroup
    function new();
      mid = new;
      mid.lvl = new;
      cov_cplx = new;
    endfunction
  endclass

  NoConstruct nc;
  ExternalClk ec;
  ComplexEvt cx;

  initial begin
    nc = new;
    ec = new;
    cx = new;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
