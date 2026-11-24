// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Event array members, waited on and triggered through a handle
class Cls;
  event eu[2];
  event e[int];
  event ew[*];
  event ed[];
  event eq[$];
  function new();
    event e0, e1, e2;
    e[5] = e0;
    ew["x"] = e1;
    ed = new[2];
    eq.push_back(e2);
  endfunction
endclass

module t;
  initial begin
    Cls c;
    bit fired;
    c = new;
    fork
      begin
        @(c.eu[1]);
        @(c.e[5]);
        @(c.ew["x"]);
        @(c.ed[1]);
        @(c.eq[0]);
        fired = 1;
      end
    join_none
    #1;
    ->c.eu[1];
    #1;
    ->c.e[5];
    #1;
    ->c.ew["x"];
    #1;
    ->c.ed[1];
    #1;
    ->c.eq[0];
    #1;
    `checkd(fired, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
