// DESCRIPTION: Verilator: Verilog Test module
//
// Repeated references to the same deferred localparam.  V3Param's
// resolveDeferredDotsReachableFrom walks a pin expression collecting
// deferred lparams to descend into, and must visit each one only once even
// when a single expression (or several pins on the same cell) references it
// many times, including via a diamond where two intermediate lparams both
// lead back to the same deferred one.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class Inner #(parameter int V = 1);
  localparam int v = V;
endclass

module Sub #(
    parameter int P = 0,
    parameter int Q = 0
) ();
  localparam int GOTP = P;
  localparam int GOTQ = Q;
endmodule

module t;
  // Deferred: value is a class::member Dot.
  localparam int d = Inner#(7)::v;

  // Diamond: both lead back to the single deferred `d`.
  localparam int left = d + 1;
  localparam int right = d + 2;

  // Same deferred lparam reached repeatedly within one pin expression...
  Sub #(
      .P(d + d + d),
      .Q(left + right)
  ) u_repeat ();

  // ...and across two pins of the same cell.
  Sub #(
      .P(d),
      .Q(d)
  ) u_bothpins ();

  initial begin
    `checkh(u_repeat.GOTP, 32'd21);
    `checkh(u_repeat.GOTQ, 32'd17);
    `checkh(u_bothpins.GOTP, 32'd7);
    `checkh(u_bothpins.GOTQ, 32'd7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
