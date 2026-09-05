// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`ifdef VERILATOR
`define IMPURE_ONE ($c(1))
`else
`define IMPURE_ONE (|($random | $random))
`endif

interface dummy_if();
  logic [7:0] signal;

  modport slave(input signal);

  modport master(output signal);
endinterface : dummy_if

module fanout #(
    parameter int N = 1
) (
  dummy_if upstream,
  dummy_if downstream[N-1:0]
);
  genvar i;
  for (i = 0; i < N; i = i + 1) assign downstream[i].signal = upstream.signal;
endmodule

module m(
  input foo,
  dummy_if.master dummy_in,
  dummy_if.slave dummy_out,
  inout bit io,
  output bit nn,
  input bar = 1
);
  dummy_if ins();
  dummy_if outs[12:0]();
  fanout#(13) ff(ins, outs);

  pullup d_0_pup (dummy_out.signal[0]);
  pullup d_1_pup (dummy_out.signal[1]);
  pulldown d_2_pdown (dummy_out.signal[2]);
  pulldown d_3_pdown (dummy_out.signal[3]);
  supply1 high;
  supply0 #1 low = dummy_in.signal[0];
endmodule

typedef struct packed {
  logic x;
  logic y;
} bar;

class Foo;
  function bit foo();
    return 1;
  endfunction
endclass

module t;
  logic D, Q;
  logic clk = 0;
  always #20 clk = ~clk;

  default clocking cb @(posedge clk);
    default input #2 output #6;
    input Q;
    output D;
  endclocking

  logic queue [$];
  logic unpackedArr [13];
  logic assocArr [integer];
  typedef logic [13:0] long_logic;
  long_logic [13:0] packedArr;
  bar barInst;
  static Foo a;
  static Foo b;
  static Foo c;
  logic kk;

  function logic f(logic a);
    return a;
  endfunction

  function logic foo();
    return 'x;
  endfunction

  dummy_if dummy_if();
  m m(foo(), dummy_if, dummy_if, kk, 'x);

  initial begin
    static integer x;
    static integer y;
    y = 2 ** x;
    x[1] = 1;
    a = new;
    c = (f(`IMPURE_ONE) ? a : b);
    if (!c.foo()) $stop;
    casex (dummy_if.signal)
      8'b01z0100x: ;
      default: $stop;
    endcase
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
