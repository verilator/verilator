// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

class Cls #(
    parameter int PARAM
);
  static int s_cls_static = 123;

  static function int s_count();
    static int s_calls = 0;
    s_calls += 1;
    return s_calls;
  endfunction

  function int count();
    static int calls = 0;
    calls += 2;
    return calls;
  endfunction
endclass

module top ();
  typedef Cls#(.PARAM(0)) Cls_t;

  Cls_t obj;

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(0);
    obj = new;
    if (obj.PARAM != 0) $stop;
    // Change the statics over time, so the trace records each change
    for (int i = 1; i <= 3; ++i) begin
      #1;
      obj.s_cls_static = 100 + i;
      if (obj.s_cls_static != 100 + i) $stop;
      if (Cls_t::s_count() != i) $stop;
      if (obj.count() != 2 * i) $stop;
    end
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
