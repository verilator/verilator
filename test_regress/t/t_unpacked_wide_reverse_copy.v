// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Graeme Smecher
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// Copies between unpacked arrays of opposite directions, of elements wider than 64 bits: the
// copy reverses the elements (VL_CVT_UNPACK_TO_UNPACK), and its result must be assigned

module t;

  logic [64:0] b[1:0];
  logic [64:0] a[0:1];  // Blocking assignment
  wire [64:0] w[0:1];  // Continuous assignment
  logic [64:0] c[0:1];  // always_comb
  logic [64:0] q[0:1];  // A conditional, one of whose branches is of the opposite direction
  logic sel;
  logic [99:0] d[1:0][0:1];  // Two dimensions, wider still, the inner one reversed
  logic [99:0] e[1:0][1:0];

  assign w = b;
  always_comb c = b;

  initial begin
    b[1] = 65'h1ffffffffffffffff;
    b[0] = 65'h0076b3e36bb2313f5;
    e[1][1] = 100'h1;
    e[1][0] = 100'h2;
    e[0][1] = 100'h3;
    e[0][0] = 100'hf_0000_0000_0000_0000_0000_0004;
    sel = 1'b1;
    #1;
    a = b;
    d = e;
    q = sel ? b : a;
    `checkh(a[0], 65'h1ffffffffffffffff);
    `checkh(a[1], 65'h0076b3e36bb2313f5);
    `checkh(w[0], 65'h1ffffffffffffffff);
    `checkh(w[1], 65'h0076b3e36bb2313f5);
    `checkh(c[0], 65'h1ffffffffffffffff);
    `checkh(c[1], 65'h0076b3e36bb2313f5);
    `checkh(q[0], 65'h1ffffffffffffffff);
    `checkh(q[1], 65'h0076b3e36bb2313f5);
    `checkh(d[1][0], 100'h1);
    `checkh(d[1][1], 100'h2);
    `checkh(d[0][0], 100'h3);
    `checkh(d[0][1], 100'hf_0000_0000_0000_0000_0000_0004);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
