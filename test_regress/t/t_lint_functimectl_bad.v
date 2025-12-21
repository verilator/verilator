// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  event e;
  logic s;

  function void calls_timing_ctl;
    @e;  // <--- Bad IEEE 1800-2023 13.4 time-controlling
    fork  // <--- Bad IEEE 1800-2023 13.4 time-controlling
    join
    fork  // <--- Bad IEEE 1800-2023 13.4 time-controlling
    join_any
    wait (s);  // <--- Bad IEEE 1800-2023 13.4 time-controlling
    // TODO wait_order (e);
    // TODO ##
    // TODO expect
  endfunction

  // No warning here
  wire [31:0] #5 __test_wire = 32'd0;
  function void f;
    int x;
  endfunction
endmodule
