// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unlike a port connection, a parameter value writing a net-type input port is
// never exempt from ASSIGNIN (and is also illegal as not constant).
interface param_if #(
    parameter int P = 1
);
endinterface

module t (
    input wire [31:0] i
);
  function automatic int f(output int o);
    o = 3;
    return 5;
  endfunction
  virtual param_if #(.P(f(i))) pif;  // ASSIGNIN: function output drives net input
endmodule
