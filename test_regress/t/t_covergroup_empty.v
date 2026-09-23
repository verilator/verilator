// DESCRIPTION: Verilator: Verilog Test module - Edge case: empty covergroup
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: Empty covergroup (no coverpoints)
// Expected: Should compile; with nothing to cover, a covergroup of nonzero weight reports 0%
// and one of zero weight 100% (IEEE 1800-2023 19.11)

module t (
    input clk
);

  logic [7:0] value;

  // Empty covergroup - no coverpoints defined
  covergroup cg_empty;
  // Intentionally empty
  endgroup

  // Empty covergroup of zero weight
  covergroup cg_empty_w0;
    option.weight = 0;
  endgroup

  cg_empty cg_inst = new;
  cg_empty_w0 cg_w0_inst = new;

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    value <= value + 1;

    cg_inst.sample();
    cg_w0_inst.sample();

    if (cyc == 5) begin
      real cov;
      cov = cg_inst.get_inst_coverage();
      $display("Empty covergroup coverage: %f%%", cov);
      $display("Empty zero-weight covergroup coverage: %f%%", cg_w0_inst.get_inst_coverage());
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
