// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Per-attempt assertion outcome counts.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;

  initial $assertpasson;

  // Overlapping attempts maturing in the same time slot
  bit imp_a = 1, imp_b = 0;
  bit chain_a = 1, chain_b = 0, chain_c = 0;
  bit range_a = 1, range_b = 0;
  int imp_pass = 0, imp_fail = 0;
  int chain_pass = 0, chain_fail = 0;
  int range_pass = 0, range_fail = 0, range_cover = 0;

  assert property (@(posedge clk) imp_a |-> ##1 imp_b) imp_pass++;
  else imp_fail++;

  assert property (@(posedge clk) chain_a ##1 chain_b ##1 chain_c) chain_pass++;
  else chain_fail++;

  assert property (@(posedge clk) range_a ##[1:2] range_b) range_pass++;
  else range_fail++;
  cover property (@(posedge clk) range_a ##[1:2] range_b) range_cover++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      imp_a <= 0;
      chain_a <= 1;
      chain_b <= 1;
      range_a <= 1;
      range_b <= 0;
    end
    else if (cyc == 1) begin
      imp_a <= 0;
      imp_b <= 0;
      chain_a <= 0;
      chain_b <= 0;
      chain_c <= 1;
      range_a <= 0;
      range_b <= 1;
    end
  end

  // The same multiplicity through the large-range ring-buffer path
  bit large_a = 0, large_b = 0;
  int large_pass = 0, large_fail = 0, large_cover = 0, large_imp_at_b = 0;

  assert property (@(posedge clk) large_a ##[1:300] large_b) large_pass++;
  else large_fail++;
  cover property (@(posedge clk) large_a ##[1:300] large_b) large_cover++;
  assert property (@(posedge clk) large_a |-> ##[1:300] large_b) if (large_b) large_imp_at_b++;

  initial begin
    @(negedge clk) large_a = 1;
    @(negedge clk) large_a = 1;
    @(negedge clk) begin
      large_a = 0;
      large_b = 1;
    end
    @(negedge clk) large_b = 0;
  end

  // Negation swaps each attempt's verdict at the tagged cycle
  bit neg_a = 0, neg_b = 0;
  bit neg_chain_a = 0, neg_chain_b = 0, neg_chain_c = 0, neg_chain_target = 0;
  bit neg_imp_a = 0, neg_imp_b = 0, neg_imp_c = 0, neg_imp_target = 0;
  int neg_fail_at_b = 0, neg_large_fail_at_b = 0;
  int neg_chain_pass = 0, neg_chain_fail = 0, neg_chain_cover = 0;
  int neg_imp_pass = 0;
  int vacuous_pass = 0, negated_vacuous_pass = 0;

  assert property (@(posedge clk) not (neg_a ##[1:2] neg_b))
  else if (neg_b) neg_fail_at_b++;
  assert property (@(posedge clk) not (neg_a ##[1:300] neg_b))
  else if (neg_b) neg_large_fail_at_b++;

  assert property (@(posedge clk) not (neg_chain_a ##1 neg_chain_b ##1 neg_chain_c)) begin
    if (neg_chain_target) neg_chain_pass++;
  end
  else begin
    if (neg_chain_target) neg_chain_fail++;
  end
  cover property (@(posedge clk) not (neg_chain_a ##1 neg_chain_b ##1 neg_chain_c))
    if (neg_chain_target) neg_chain_cover++;

  // One nonvacuous and one vacuous pass in the same clock
  assert property (@(posedge clk) neg_imp_a |-> not (neg_imp_b ##1 neg_imp_c))
    if (neg_imp_target) neg_imp_pass++;

  assert property (@(posedge clk) 0 |-> ##1 1) vacuous_pass++;
  assert property (@(posedge clk) 0 |-> not (##1 1)) negated_vacuous_pass++;

  initial begin
    @(negedge clk) begin
      neg_a = 1;
      neg_chain_a = 1;
      neg_imp_a = 1;
      neg_imp_b = 1;
    end
    @(negedge clk) begin
      neg_a = 1;
      neg_chain_a = 1;
      neg_chain_b = 1;
      neg_imp_a = 0;
      neg_imp_b = 0;
      neg_imp_target = 1;
    end
    @(negedge clk) begin
      neg_a = 0;
      neg_b = 1;
      neg_chain_a = 0;
      neg_chain_b = 0;
      neg_chain_c = 1;
      neg_chain_target = 1;
      neg_imp_target = 0;
    end
    @(negedge clk) begin
      neg_b = 0;
      neg_chain_target = 0;
    end
  end

  // Property-case branches of different lengths failing on the same tick
  logic [1:0] selector;
  int case_fail = 0;

  always_comb begin
    if (cyc == 2) selector = 0;
    else if (cyc == 3) selector = 1;
    else selector = 2;
  end

  assert property (@(posedge clk) case (selector) 0: 1'b1 ##2 1'b0; 1: 1'b1 ##1 1'b0; default: 1'b1;
  endcase)
  else case_fail++;

  always @(negedge clk) begin
    if (cyc == 12) begin
      `checkd(imp_pass, 10);
      `checkd(imp_fail, 1);
      `checkd(chain_pass, 2);
      `checkd(chain_fail, 11);
      `checkd(range_pass, 1);
      `checkd(range_fail, 10);
      `checkd(range_cover, 1);
      `checkd(large_pass, 1);
      `checkd(large_fail, 10);
      `checkd(large_cover, 1);
      `checkd(large_imp_at_b, 2);
      `checkd(neg_fail_at_b, 1);
      `checkd(neg_large_fail_at_b, 1);
      `checkd(neg_chain_pass, 2);
      `checkd(neg_chain_fail, 2);
      `checkd(neg_chain_cover, 1);
      `checkd(neg_imp_pass, 2);
      `checkd(vacuous_pass, 12);
      `checkd(negated_vacuous_pass, 12);
      `checkd(case_fail, 2);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
