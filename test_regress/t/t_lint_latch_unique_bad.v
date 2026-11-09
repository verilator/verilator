// DESCRIPTION: Verilator: Verilog Test module for unique if latch checks
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Christopher Onyiuke
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic a,
    input logic b,
    output logic o1,
    output logic o2,
    output logic o3,
    output logic o4,
    output logic o4b,
    output logic o5
);

  // unique0 permits no condition to match, so the missing else is a latch path.
  always_comb begin
    unique0 if (a) o1 = 1'b1;
  end

  // A plain if/else-if chain without a final else is not exhaustive.
  always_comb begin
    if (a) o2 = 1'b1;
    else if (b) o2 = 1'b0;
  end

  // A nested if in the then branch must not inherit the outer unique chain's
  // exhaustive state.
  always_comb begin
    unique if (a) begin
      if (b) o3 = 1'b1;
    end
  end

  // A branch of an exhaustive unique if that skips an assignment is still a latch.
  always_comb begin
    unique if (a) begin
      o4b = 1'b1;
    end
    else begin
      o4b = 1'b0;
      o4 = 1'b1;
    end
  end

  // A non-if else block ends the unique else-if chain.
  always_comb begin
    unique if (a) o5 = 1'b1;
    else begin
      // Keep this as a block so V3Const does not fold the else into an else-if.
      $display("Taking the unique else branch");
      o5 = 1'b0;
    end
  end

endmodule
