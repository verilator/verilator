// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

function automatic int f(int x);
  int n;
  for (int i = 0; i < x; ++i) begin
    ++n;
  end
  return n;
endfunction

module t (
    output logic [f(4):0] o4,  // Should simulate
    output logic [f(5):0] o5  // Should NOT simulate
);

endmodule
