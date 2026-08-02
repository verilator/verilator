// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Marco Bartoli
// SPDX-License-Identifier: CC0-1.0

// A 'dist' weights the choice among its items but does not require any one of
// them (IEEE 1800-2023 18.5.4).  The weighted pick must therefore yield to a
// hard constraint, including one that only relates two variables indirectly.
//
// Here operand_a and operand_b each carry their own distribution, and a hard
// implication ties them together when force_equal is set.  The two buckets are
// drawn independently, so on the roughly one draw in five where force_equal is
// 1 they usually disagree.  If the picks were hard, that disagreement would
// have no solution and randomize() would return 0; the implication must win
// instead.
//
// t_constraint_dist_inline group J covers a hard constraint excluding a bucket
// of a single variable.  This is the cross-variable form, from issue #8026.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`define N 200

class GcdRequest;
  localparam int GCD_RAND_MAX = 31;
  localparam int GCD_INTERIOR_LO = 1;
  localparam int GCD_INTERIOR_HI = 30;

  rand int operand_a;
  rand int operand_b;
  rand bit force_equal;
  rand bit rsp_ready_before_valid;

  constraint c_edge_bias {
    operand_a dist {
      0                                   := 1,
      GCD_RAND_MAX                        := 1,
      [GCD_INTERIOR_LO : GCD_INTERIOR_HI] :/ 10
    };
    operand_b dist {
      0                                   := 1,
      GCD_RAND_MAX                        := 1,
      [GCD_INTERIOR_LO : GCD_INTERIOR_HI] :/ 10
    };
    force_equal dist {
      0 := 4,
      1 := 1
    };
    (force_equal == 1) -> (operand_a == operand_b);
    rsp_ready_before_valid dist {
      0 := 3,
      1 := 1
    };
  }
endclass

module t;
  initial begin
    automatic GcdRequest request = new;
    int result;
    int equal_trials;

    for (int i = 0; i < `N; i++) begin
      // Must stay satisfiable even when the independently drawn operand
      // preferences disagree; the hard implication takes priority.
      result = request.randomize();
      `checkd(result, 1);
      if (request.force_equal) begin
        equal_trials++;
        `checkd(request.operand_a, request.operand_b);
      end
      `checkd(request.operand_a >= 0, 1);
      `checkd(request.operand_a <= request.GCD_RAND_MAX, 1);
      `checkd(request.operand_b >= 0, 1);
      `checkd(request.operand_b <= request.GCD_RAND_MAX, 1);
    end

    // Without this the run above proves nothing, as the implication would
    // never have been exercised.
    `checkd(equal_trials > 0, 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
