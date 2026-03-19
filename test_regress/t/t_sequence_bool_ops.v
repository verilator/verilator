// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0
module t (
    input clk
);

  int cyc = 0;
  logic a, b, c;
  int and_pass_count = 0;
  int or_pass_count = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      0: begin a <= 0; b <= 0; c <= 0; end
      1: begin a <= 1; b <= 0; c <= 1; end
      2: begin a <= 0; b <= 1; c <= 1; end
      3: begin a <= 1; b <= 1; c <= 1; end
      4: begin a <= 1; b <= 1; c <= 1; end
      default: begin a <= 1; b <= 1; c <= 1; end
    endcase
    if (cyc == 10) begin
      if (and_pass_count == 0) begin
        $display("%%Error: 'and' assertion never matched non-vacuously");
        $stop;
      end
      if (or_pass_count == 0) begin
        $display("%%Error: 'or' assertion never matched non-vacuously");
        $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Count non-vacuous matches to verify runtime evaluation
  always @(posedge clk) if (a && b) and_pass_count <= and_pass_count + 1;
  always @(posedge clk) if (a || b) or_pass_count <= or_pass_count + 1;

  // Boolean 'and' in sequence context: both a and b true implies c
  assert property (@(posedge clk) disable iff (cyc < 3) (a and b) |-> c);
  // Boolean 'or' in sequence context: at least one true implies c
  assert property (@(posedge clk) disable iff (cyc < 3) (a or b) |-> c);
  // 'and' with constant true
  assert property (@(posedge clk) disable iff (cyc < 3) (a and 1'b1) |-> c);
  // 'or' with constant false -- reduces to just 'a'
  assert property (@(posedge clk) disable iff (cyc < 3) (a or 1'b0) |-> c);

endmodule
