// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  typedef struct packed {logic [1:0][31:0] bar;} T;
  localparam T t = 64'h87654321_deadbeef;
endpackage

module foo #(
    parameter type T = int,
    parameter T t = 0
) ();
  initial begin
    `checkh(t.bar[0], 32'hdeadbeef);
    `checkh(t.bar[1], 32'h87654321);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module top;
  foo #(
      .T(pkg::T),
      .t(pkg::t)
  ) u_foo ();
endmodule
