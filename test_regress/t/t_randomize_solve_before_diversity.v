// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

// solve...before phased solving (IEEE 1800-2023 18.5.9) is only checked
// elsewhere for feasibility (does a valid solution exist), never for the
// LRM's own distribution guarantee on the "before" variable. The LRM's own
// worked example for this exact shape (18.5.9): "the order constraint
// instructs the solver to solve for s before solving for d. The effect is
// that s is now chosen 0 or 1 with 50%/50% probability." Prior to the fix
// this targets, the diversity constraint built for a phase sampled bits
// from every rand var in the class rather than just that phase's own layer,
// so a narrow "before" variable sharing a constraint with a wider "after"
// variable could end up with a diversity constraint built entirely out of
// the "after" variable's bits -- leaving the "before" variable stuck at
// whatever the solver's first, non-randomized check-sat happened to assign
// it (0/20000 "before" draws landed on 1, instead of the expected ~50%).
class SolveBeforeDiversity;
  rand bit s;
  rand bit [7:0] d;
  constraint c {
    s -> d == 0;
  }
  constraint order {
    solve s before d;
  }
endclass

module t;
  parameter int N = 8000;  // randomize() calls
  parameter int TOL_PCT = 30;  // +-% tolerance on expected count

  initial begin
    int randomize_result;
    automatic SolveBeforeDiversity obj = new();
    int s_count;
    s_count = 0;
    repeat (N) begin
      randomize_result = obj.randomize();
      `checkd(randomize_result, 1);
      if (obj.s) begin
        `checkd(obj.d, 8'h00)
      end
      if (obj.s) s_count++;
    end
    `check_range(s_count, (N / 2) * (100 - TOL_PCT) / 100, (N / 2) * (100 + TOL_PCT) / 100)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
