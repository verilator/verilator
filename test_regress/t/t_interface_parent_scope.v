// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Driss Hafdi.
// SPDX-License-Identifier: CC0-1.0

interface Foo;
  logic quux;
endinterface

module Bar;
  // Issue# 1623 - seems legal
  always_comb foo.quux = '0;
endmodule

module Baz;
  Foo foo ();
  Bar bar ();
endmodule

module t;

  Baz baz ();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
