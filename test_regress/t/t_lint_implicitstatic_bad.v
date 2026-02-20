// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  class C;
    task t;
      int c_no_has_init = 1;  // Ok
      automatic int c_automatic_has_init = 1;  // Ok
      static int c_static_has_init = 1;  // Ok
    endtask
  endclass

  always @(posedge clk) begin
    int implicit_warn = 1;  // <--- Warning: IMPLICITSTATIC
    localparam int OK = 2;  // Ok
  end

  task t_implicit_static();
    int t_no_has_init = 1;  // <--- Warning: IMPLICIT STATIC
    automatic int t_automatic_has_init = 1;  // Ok
    static int t_static_has_init = 1;  // Ok
    localparam int ONE = 1;  // Ok
    ++t_no_has_init;
  endtask

  function int f_implicit_static();
    int f_no_has_init = 1;  // <--- Warning: IMPLICIT STATIC
    automatic int f_automatic_has_init = 1;  // Ok
    static int f_static_has_init = 1;  // Ok
    localparam int ONE = 1;  // Ok
    ++f_no_has_init;
    return ONE;
  endfunction

  initial begin
    int i_no_has_init = 1;  // <--- Warning: IMPLICIT STATIC
    automatic int i_automatic_has_init = 1;  // Ok
    static int i_static_has_init = 1;  // Ok
    $finish;
  end

endmodule
