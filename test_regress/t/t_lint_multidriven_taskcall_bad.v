// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic sel,
    input logic sel2,
    input logic d,
    output logic out
);

  task automatic do_stuff(input logic din);
    out = din;
  endtask

  // Driver #1 (via task call)
  always_comb begin
    out = 1'b0;
    if (sel) do_stuff(d);
  end

  // Driver #2 (separate process)
  // I only want the MULTIDRIVEN.
  /* verilator lint_off LATCH */
  always_comb begin
    if (sel2) out = 1'b1;
  end
  /* verilator lint_on LATCH */

endmodule
