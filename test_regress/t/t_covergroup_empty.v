// DESCRIPTION: Verilator: Verilog Test module - Edge case: empty covergroup
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: Empty covergroup (no coverpoints)
// Expected: Should compile, coverage should be 100% (nothing to cover)

module t (/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  logic [7:0] value;

  // Empty covergroup - no coverpoints defined
  covergroup cg_empty;
    // Intentionally empty
  endgroup

  cg_empty cg_inst = new;

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    value <= value + 1;

    cg_inst.sample();

    if (cyc == 5) begin
      real cov;
      cov = cg_inst.get_inst_coverage();
      $display("Empty covergroup coverage: %f%%", cov);
      $write("*-* All Finished *-*\n");
      $finish;
    end

    if (cyc > 10) begin
      $display("ERROR: Test timed out");
      $stop;
    end
  end
endmodule
