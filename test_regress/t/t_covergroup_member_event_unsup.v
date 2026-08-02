// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Embedded covergroup events that cannot be approximated without --timing must
// emit COVERIGN rather than silently producing zero coverage.

module t;
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

  ExternalClk ec;
  ComplexEvt cx;

  initial begin
    ec = new;
    cx = new;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
