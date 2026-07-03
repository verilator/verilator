// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  logic [63:0] crc = 64'h5aef0c8dd70a4497;
  logic a, b;
  int cyc = 0;

  int n_imp_no = 0;  // cover property (a |=> b)  -- non-overlapped implication
  int n_imp_ov = 0;  // cover property (a |-> b)  -- overlapped implication
  int n_seq = 0;  // cover property (a ##1 b)  -- identity with |=>
  int n_seq0 = 0;  // cover property (a ##0 b)  -- identity with |->
  int n_bool = 0;  // cover property (a)        -- bare boolean baseline
  int n_named = 0;  // cover property (named pr) -- identity with |=>

  default clocking cb @(posedge clk);
  endclocking

  assign a = crc[0];
  assign b = crc[5];

  property pr;
    a |=> b;
  endproperty

  cp_imp_no :
  cover property (a |=> b) n_imp_no++;
  cp_imp_ov :
  cover property (a |-> b) n_imp_ov++;
  cp_seq :
  cover property (a ##1 b) n_seq++;
  cp_seq0 :
  cover property (a ##0 b) n_seq0++;
  cp_bool :
  cover property (a) n_bool++;
  cp_named :
  cover property (pr) n_named++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[1] ^ crc[0]};
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  final begin
    // A cover of an implication counts only non-vacuous matches (IEEE
    // 1800-2023 16.15.2): the antecedent must match. So it is identical to the
    // corresponding sequence cover, not the vacuous implication value.
    `checkd(n_imp_no, n_seq);  // Other sims: pass, 73
    `checkd(n_imp_ov, n_seq0);  // Other sims: pass, 45
    // A named-property cover lowers the same implication, so it also counts
    // non-vacuously (regression guard for the property-inlining path).
    `checkd(n_named, n_imp_no);
    `checkd(n_imp_no, 28);
    `checkd(n_imp_ov, 27);  // Other sims: pass, 73
    `checkd(n_seq, 28);  // Other sims: 45, 27
    `checkd(n_seq0, 27);
    `checkd(n_bool, 55);  // Other sims: pass, 25
    `checkd(n_named, 28);  // Other sims: 73, 54, 54
  end

endmodule
