// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// Case statements that become a "tiny" lookup table, followed by cases that must
// not be converted to one. Each output is compared against an equivalent reference
// computed without a case statement, so the reference itself is never tabled.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 1'b0;
  always #5 clk = ~clk;

  logic [31:0] cyc = 0;

  // Accept A: single output, blocking assignment, all selector values covered.
  wire [2:0] accept_a_in = cyc[2:0];
  logic [3:0] accept_a_out, accept_a_ref;
  always_comb
    case (accept_a_in)
      3'd0: accept_a_out = 4'd3;
      3'd1: accept_a_out = 4'd4;
      3'd2: accept_a_out = 4'd5;
      3'd3: accept_a_out = 4'd6;
      3'd4: accept_a_out = 4'd7;
      3'd5: accept_a_out = 4'd8;
      3'd6: accept_a_out = 4'd9;
      3'd7: accept_a_out = 4'd10;
    endcase
  assign accept_a_ref = 4'd3 + {1'b0, accept_a_in};

  // Accept B: single output, non-blocking assignment, with a default value set before
  //         the case and not all selector values covered.
  logic [3:0] accept_b_out, accept_b_ref;
  // verilator lint_off CASEINCOMPLETE
  always_ff @(posedge clk) begin
    accept_b_out <= 4'hf;
    case (cyc[1:0])
      2'b00: accept_b_out <= 4'h1;
      2'b01: accept_b_out <= 4'h2;
    endcase
  end
  // verilator lint_on CASEINCOMPLETE
  always_ff @(posedge clk)
    accept_b_ref <= (cyc[1:0] == 2'b00) ? 4'h1 : (cyc[1:0] == 2'b01) ? 4'h2 : 4'hf;

  // Accept C: two outputs of different widths, blocking assignment, with a default branch.
  logic [2:0] accept_c_out_0, accept_c_ref_0;
  logic [3:0] accept_c_out_1, accept_c_ref_1;
  always_comb
    case (cyc[1:0])
      2'b00: begin
        accept_c_out_0 = 3'd1;
        accept_c_out_1 = 4'd6;
      end
      2'b01: begin
        accept_c_out_0 = 3'd2;
        accept_c_out_1 = 4'd5;
      end
      default: begin
        accept_c_out_0 = 3'd0;
        accept_c_out_1 = 4'd7;
      end
    endcase
  assign accept_c_ref_0 = (cyc[1:0] == 2'b00) ? 3'd1 : (cyc[1:0] == 2'b01) ? 3'd2 : 3'd0;
  assign accept_c_ref_1 = (cyc[1:0] == 2'b00) ? 4'd6 : (cyc[1:0] == 2'b01) ? 4'd5 : 4'd7;

  // Accept D: two outputs, non-blocking assignment, empty default branch, with default
  //         values set before the case.
  logic [2:0] accept_d_out_0, accept_d_ref_0;
  logic [2:0] accept_d_out_1, accept_d_ref_1;
  always_ff @(posedge clk) begin
    accept_d_out_0 <= 3'd0;
    accept_d_out_1 <= 3'd7;
    case (cyc[1:0])
      2'b00: begin
        accept_d_out_0 <= 3'd1;
        accept_d_out_1 <= 3'd6;
      end
      2'b01: begin
        accept_d_out_0 <= 3'd2;
        accept_d_out_1 <= 3'd5;
      end
      default: begin
      end
    endcase
  end
  always_ff @(posedge clk) begin
    accept_d_ref_0 <= (cyc[1:0] == 2'b00) ? 3'd1 : (cyc[1:0] == 2'b01) ? 3'd2 : 3'd0;
    accept_d_ref_1 <= (cyc[1:0] == 2'b00) ? 3'd6 : (cyc[1:0] == 2'b01) ? 3'd5 : 3'd7;
  end

  // Accept E: casez with a don't-care bit.
  logic [3:0] accept_e_out, accept_e_ref;
  always_comb
    casez (cyc[1:0])
      2'b1?: accept_e_out = 4'ha;
      2'b0?: accept_e_out = 4'hb;
    endcase
  assign accept_e_ref = cyc[1] ? 4'ha : 4'hb;

  // Accept F: an item that can never match, and an item listing multiple values.
  logic [3:0] accept_f_out, accept_f_ref;
  // verilator lint_off CASEWITHX
  always_comb
    casez (cyc[1:0])
      2'bx0: accept_f_out = 4'h0;  // X can never match in 2-state
      2'b01, 2'b11: accept_f_out = 4'h5;  // lists two values
      default: accept_f_out = 4'h9;
    endcase
  // verilator lint_on CASEWITHX
  assign accept_f_ref = (cyc[1:0] == 2'b01 || cyc[1:0] == 2'b11) ? 4'h5 : 4'h9;

  // Accept G: items assign different subsets of two outputs, with default values (and an
  //         unrelated output) set before the case.
  logic [3:0] accept_g_out_0, accept_g_ref_0;
  logic [3:0] accept_g_out_1, accept_g_ref_1;
  logic [3:0] accept_g_out_2, accept_g_ref_2;
  // verilator lint_off CASEINCOMPLETE
  always_comb begin
    accept_g_out_0 = 4'h0;
    accept_g_out_1 = 4'hf;
    accept_g_out_2 = 4'h3;  // not assigned in the case
    case (cyc[1:0])
      2'b00: accept_g_out_0 = 4'h1;
      2'b01: accept_g_out_1 = 4'h2;
    endcase
  end
  // verilator lint_on CASEINCOMPLETE
  assign accept_g_ref_0 = (cyc[1:0] == 2'b00) ? 4'h1 : 4'h0;
  assign accept_g_ref_1 = (cyc[1:0] == 2'b01) ? 4'h2 : 4'hf;
  assign accept_g_ref_2 = 4'h3;

  // Accept H: single output, non-blocking assignment, all selector values covered.
  logic [3:0] accept_h_out, accept_h_ref;
  always_ff @(posedge clk)
    case (cyc[1:0])
      2'b00: accept_h_out <= 4'h1;
      2'b01: accept_h_out <= 4'h2;
      2'b10: accept_h_out <= 4'h4;
      2'b11: accept_h_out <= 4'h8;
    endcase
  always_ff @(posedge clk) accept_h_ref <= 4'h1 << cyc[1:0];

  // Accept I: unique0 enum case; the selector may hold an out-of-range value.
  typedef enum logic [1:0] {
    E0,
    E1,
    E2
  } e_t;
  e_t accept_i_in;
  assign accept_i_in = e_t'(cyc[1:0]);
  logic [3:0] accept_i_out, accept_i_ref;
  always_comb begin
    accept_i_out = 4'hf;
    unique0 case (accept_i_in)
      E0: accept_i_out = 4'h1;
      E1: accept_i_out = 4'h2;
      E2: accept_i_out = 4'h3;
    endcase
  end
  assign accept_i_ref = (cyc[1:0] == 2'd0) ? 4'h1
                      : (cyc[1:0] == 2'd1) ? 4'h2
                      : (cyc[1:0] == 2'd2) ? 4'h3 : 4'hf;

  // Accept J: wide output, materialized as a normal (not tiny) lookup table.
  logic [8:0] accept_j_out, accept_j_ref;
  always_comb
    case (cyc[3:0])
      4'd0: accept_j_out = 9'h001;
      4'd1: accept_j_out = 9'h002;
      4'd2: accept_j_out = 9'h004;
      4'd3: accept_j_out = 9'h008;
      default: accept_j_out = 9'h010;
    endcase
  assign accept_j_ref = (cyc[3:0] < 4'd4) ? (9'h1 << cyc[3:0]) : 9'h010;

  // Accept K: a non-constant assignment precedes the case.
  logic [3:0] accept_k_out_0, accept_k_ref_0;
  logic [3:0] accept_k_out_1, accept_k_ref_1;
  always_comb begin
    accept_k_out_1 = cyc[3:0] ^ 4'ha;  // non-constant value
    case (cyc[1:0])
      2'b00: accept_k_out_0 = 4'h1;
      2'b01: accept_k_out_0 = 4'h2;
      2'b10: accept_k_out_0 = 4'h4;
      2'b11: accept_k_out_0 = 4'h8;
    endcase
  end
  assign accept_k_ref_0 = 4'h1 << cyc[1:0];
  assign accept_k_ref_1 = cyc[3:0] ^ 4'ha;

  // Accept L: the same output is given a default value twice before the case.
  logic [3:0] accept_l_out, accept_l_ref;
  // verilator lint_off CASEINCOMPLETE
  always_comb begin
    accept_l_out = 4'h1;
    accept_l_out = 4'h6;  // assigned a second time before the case
    case (cyc[1:0])
      2'b00: accept_l_out = 4'h2;
      2'b01: accept_l_out = 4'h3;
    endcase
  end
  // verilator lint_on CASEINCOMPLETE
  assign accept_l_ref = (cyc[1:0] == 2'd0) ? 4'h2 : (cyc[1:0] == 2'd1) ? 4'h3 : 4'h6;

  // The cases below are intentionally NOT converted to a lookup table.

  // Reject A: an item whose body is not a simple assignment.
  logic [3:0] reject_a_out, reject_a_ref;
  always_comb begin
    reject_a_out = 4'h0;
    case (cyc[1:0])
      2'b00: reject_a_out = 4'h1;
      2'b01: if (cyc[0]) reject_a_out = 4'h2;  // not a simple assignment
      default: reject_a_out = 4'h3;
    endcase
  end
  assign reject_a_ref = (cyc[1:0] == 2'd0) ? 4'h1 : (cyc[1:0] == 2'd1) ? 4'h2 : 4'h3;

  // Reject B: an item assigns through a variable bit-select (the index is read).
  logic [3:0] reject_b_out, reject_b_ref;
  always_comb begin
    reject_b_out = 4'h0;
    case (cyc[1:0])
      2'b00: reject_b_out[cyc[1:0]] = 1'b1;
      default: reject_b_out = 4'h5;
    endcase
  end
  assign reject_b_ref = (cyc[1:0] == 2'd0) ? 4'h1 : 4'h5;

  // Reject C: an item assigns the same output twice.
  logic [3:0] reject_c_out, reject_c_ref;
  always_comb begin
    reject_c_out = 4'h0;
    case (cyc[1:0])
      2'b00: begin
        reject_c_out = 4'h1;
        reject_c_out = 4'h2;
      end
      default: reject_c_out = 4'h3;
    endcase
  end
  assign reject_c_ref = (cyc[1:0] == 2'd0) ? 4'h2 : 4'h3;

  // Reject D: a non-constant case-item value.
  logic [1:0] reject_d_in;
  assign reject_d_in = cyc[1:0];
  logic [3:0] reject_d_out, reject_d_ref;
  always_comb begin
    reject_d_out = 4'h0;
    case (cyc[1:0])
      reject_d_in: reject_d_out = 4'h7;  // non-constant item value
      default: reject_d_out = 4'h9;
    endcase
  end
  assign reject_d_ref = 4'h7;  // reject_d_in always equals the case expression

  // Reject E: all items are empty.
  logic [3:0] reject_e_out, reject_e_ref;
  always_comb begin
    reject_e_out = 4'h7;
    case (cyc[2:0])
      3'd0: ;
      3'd1: ;
      3'd2: ;
      3'd3: ;
      3'd4: ;
      3'd5: ;
      3'd6: ;
      3'd7: ;
    endcase
  end
  assign reject_e_ref = 4'h7;

  // Reject F: an item uses a delayed (intra-assignment) assignment.
  logic [3:0] reject_f_out, reject_f_ref;
  always_ff @(posedge clk)
    case (cyc[1:0])
      2'b00: reject_f_out <= #1 4'h1;  // delayed assignment
      default: reject_f_out <= 4'h2;
    endcase
  always_ff @(posedge clk)
    if (cyc[1:0] == 2'b00) reject_f_ref <= #1 4'h1;
    else reject_f_ref <= 4'h2;

  // Reject G: an output assigned with both blocking and non-blocking assignments. The three
  //         variants exercise the distinct ways the assignment kinds conflict. The deliberate
  //         mixing warnings are waived.
  // verilator lint_off BLKANDNBLK
  // verilator lint_off COMBDLY
  // verilator lint_off CASEINCOMPLETE
  // Variant 0: an item mixes a blocking and a non-blocking assignment to the same output.
  logic [3:0] reject_g_out_0, reject_g_ref_0;
  always_comb
    case (cyc[1:0])
      2'b00: reject_g_out_0 = 4'h1;
      2'b01: reject_g_out_0 <= 4'h2;
      default: reject_g_out_0 = 4'h3;
    endcase
  assign reject_g_ref_0 = (cyc[1:0] == 2'b00) ? 4'h1 : (cyc[1:0] == 2'b01) ? 4'h2 : 4'h3;
  // Variant 1: blocking items, but the pre-case default is a non-blocking assignment.
  logic [3:0] reject_g_out_1, reject_g_ref_1;
  always_comb begin
    reject_g_out_1 <= 4'h0;
    case (cyc[1:0])
      2'b00: reject_g_out_1 = 4'h1;
      2'b01: reject_g_out_1 = 4'h2;
    endcase
  end
  assign reject_g_ref_1 = (cyc[1:0] == 2'b00) ? 4'h1 : (cyc[1:0] == 2'b01) ? 4'h2 : 4'h0;
  // Variant 2: non-blocking items, but the pre-case default is a blocking assignment.
  logic [3:0] reject_g_out_2, reject_g_ref_2;
  always_comb begin
    reject_g_out_2 = 4'h0;
    case (cyc[1:0])
      2'b00: reject_g_out_2 <= 4'h1;
      2'b01: reject_g_out_2 <= 4'h2;
    endcase
  end
  assign reject_g_ref_2 = (cyc[1:0] == 2'b00) ? 4'h1 : (cyc[1:0] == 2'b01) ? 4'h2 : 4'h0;
  // verilator lint_on CASEINCOMPLETE
  // verilator lint_on COMBDLY
  // verilator lint_on BLKANDNBLK

  // Reject H: items assign a real (non-packed) output.
  real reject_h_out, reject_h_ref;
  always_comb
    case (cyc[1:0])
      2'b00: reject_h_out = 1.5;
      2'b01: reject_h_out = 2.5;
      default: reject_h_out = 9.0;
    endcase
  always_comb reject_h_ref = (cyc[1:0] == 2'b00) ? 1.5 : (cyc[1:0] == 2'b01) ? 2.5 : 9.0;

  // Reject I: items assign a string (non-packed) output.
  string reject_i_out, reject_i_ref;
  always_comb
    case (cyc[1:0])
      2'b00: reject_i_out = "zero";
      2'b01: reject_i_out = "one";
      default: reject_i_out = "other";
    endcase
  always_comb reject_i_ref = (cyc[1:0] == 2'b00) ? "zero" : (cyc[1:0] == 2'b01) ? "one" : "other";

  // Test driver/checker
  always @(posedge clk) begin
    `checkh(accept_a_out, accept_a_ref);
    `checkh(accept_b_out, accept_b_ref);
    `checkh(accept_c_out_0, accept_c_ref_0);
    `checkh(accept_c_out_1, accept_c_ref_1);
    `checkh(accept_d_out_0, accept_d_ref_0);
    `checkh(accept_d_out_1, accept_d_ref_1);
    `checkh(accept_e_out, accept_e_ref);
    `checkh(accept_f_out, accept_f_ref);
    `checkh(accept_g_out_0, accept_g_ref_0);
    `checkh(accept_g_out_1, accept_g_ref_1);
    `checkh(accept_g_out_2, accept_g_ref_2);
    `checkh(accept_h_out, accept_h_ref);
    `checkh(accept_i_out, accept_i_ref);
    `checkh(accept_j_out, accept_j_ref);
    `checkh(accept_k_out_0, accept_k_ref_0);
    `checkh(accept_k_out_1, accept_k_ref_1);
    `checkh(accept_l_out, accept_l_ref);
    `checkh(reject_a_out, reject_a_ref);
    `checkh(reject_b_out, reject_b_ref);
    `checkh(reject_c_out, reject_c_ref);
    `checkh(reject_d_out, reject_d_ref);
    `checkh(reject_e_out, reject_e_ref);
    `checkh(reject_f_out, reject_f_ref);
    `checkh(reject_g_out_0, reject_g_ref_0);
    `checkh(reject_g_out_1, reject_g_ref_1);
    `checkh(reject_g_out_2, reject_g_ref_2);
    `checkr(reject_h_out, reject_h_ref);
    `checks(reject_i_out, reject_i_ref);

    cyc <= cyc + 32'd1;
    if (cyc == 32'd32) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
