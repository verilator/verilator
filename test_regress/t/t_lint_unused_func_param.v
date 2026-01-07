// DESCRIPTION: Verilator: Test for false positive UNUSEDSIGNAL in unused functions
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

`default_nettype none
`timescale 1ns/1ps

module t;
   foo foo_inst();
endmodule

module foo(
  input  wire i,
  output wire o
);
  function integer foo_func;
    input integer n;
    begin
      foo_func = n;
    end
  endfunction
  assign o = i;
endmodule

