// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
  // Outputs
  o
  );

  // verilator lint_off UNDRIVEN

  function integer no_rtn();  // <--- Warning: No return
  endfunction

  localparam WIDTH = no_rtn();

  output [WIDTH-1:0] o;

endmodule
