// DESCRIPTION: Verilator: Verilog Test module - parameter/localparam refs in bins
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: Referencing a parameter/localparam identifier inside a covergroup
// `bins` value or range. This previously triggered an internal error
// (V3WidthCommit.cpp: No dtype) because the folded constant had no dtype.
// Expected: compiles and the bounds behave exactly like numeric literals.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t #(
    parameter int PMIN = -100
) (
    input clk
);

  localparam int LMAX = 100;

  int signed value;

  covergroup cg;
    cp: coverpoint value {
      bins negative = {[PMIN : -1]};  // parameter as range lower bound
      bins zero = {0};
      bins positive = {[1 : LMAX]};  // localparam as range upper bound
      bins maxv = {LMAX};  // localparam as single value
      bins minv = {PMIN};  // parameter as single value
    }
  endgroup

  cg cg_inst = new;

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    case (cyc)
      0: value <= -100;  // Hit negative + minv
      1: value <= 0;  // Hit zero
      2: value <= 50;  // Hit positive
      3: value <= 100;  // Hit positive (dup) + maxv
      4: begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    endcase

    cg_inst.sample();

    // Coverage progression (NBA committed before sample() within always block).
    // No sample runs on the $finish cycle; statements after $finish are skipped.
    // cyc=0: value=-100 -> negative + minv      -> 2/5=40%
    // cyc=1: value=0    -> zero                 -> 3/5=60%
    // cyc=2: value=50   -> positive             -> 4/5=80%
    // cyc=3: value=100  -> positive(dup) + maxv -> 5/5=100%
    if (cyc == 0) begin
      `checkr(cg_inst.get_inst_coverage(), 40.0);
    end
    if (cyc == 1) begin
      `checkr(cg_inst.get_inst_coverage(), 60.0);
    end
    if (cyc == 2) begin
      `checkr(cg_inst.get_inst_coverage(), 80.0);
    end
    if (cyc == 3) begin
      `checkr(cg_inst.get_inst_coverage(), 100.0);
    end
  end
endmodule
