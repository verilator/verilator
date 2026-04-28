// DESCRIPTION: Verilator: Verilog Test module - Edge case: negative value ranges
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: Bins with negative value ranges
// Expected: Should handle negative numbers correctly

module t (/*AUTOARG*/
  // Inputs
  clk
  );
  `define stop $stop
  `define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

  input clk;

  int signed value;

  /* verilator lint_off CMPCONST */
  covergroup cg;
    cp_neg: coverpoint value {
      bins negative = {[-100:-1]};
      bins zero = {0};
      bins positive = {[1:100]};
      bins mixed = {[-10:10]};
    }
  endgroup
  /* verilator lint_on CMPCONST */

  cg cg_inst = new;

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    case (cyc)
      0: value <= -50;    // Hit negative bin
      1: value <= 0;      // Hit zero bin
      2: value <= 50;     // Hit positive bin
      3: value <= -5;     // Hit mixed bin (also negative)
      4: value <= 5;      // Hit mixed bin (also positive)
      5: begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    endcase

    cg_inst.sample();

    // Coverage progression (NBA assignments committed before sample() within always block)
    // cyc=0: value=-50 → hits 'negative' only → 1/4=25%
    // cyc=1: value=0   → hits 'zero' + 'mixed' (both match) → 3/4=75%
    // cyc=2: value=50  → hits 'positive' → 4/4=100%
    // cyc=3: value=-5  → 'negative' + 'mixed' already hit → 4/4=100%
    // cyc=4: value=5   → 'positive' + 'mixed' already hit → 4/4=100%
    if (cyc == 0) begin `checkr(cg_inst.get_inst_coverage(), 25.0); end
    if (cyc == 1) begin `checkr(cg_inst.get_inst_coverage(), 75.0); end
    if (cyc == 2) begin `checkr(cg_inst.get_inst_coverage(), 100.0); end
    if (cyc == 3) begin `checkr(cg_inst.get_inst_coverage(), 100.0); end
    if (cyc == 4) begin `checkr(cg_inst.get_inst_coverage(), 100.0); end

    if (cyc > 10) begin
      $display("ERROR: Test timed out");
      $stop;
    end
  end
endmodule
