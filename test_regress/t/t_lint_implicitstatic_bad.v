// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  initial begin
    int static_ok = 1;  // Obvious as is in initial
  end

  always @(posedge clk) begin
    int implicit_warn = 1;  // <--- Warning: IMPLICITSTATIC
    localparam int NO_WARN = 2;  // No warning here
  end

  function int f_implicit_static();
    int cnt = 0;  // <--- Warning: IMPLICIT STATIC
    return ++cnt;
  endfunction

  task f_implicit_static();
    int cnt = 0;  // <--- Warning: IMPLICIT STATIC
    ++cnt;
  endtask

  function int f_no_implicit_static();
    localparam int ONE = 1;  // No warning here
    return ONE;
  endfunction

  task t_no_implicit_static();
    localparam TWO = 2;  // No warning here
  endtask

endmodule
