// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// Case statements that become a "normal" (constant-pool) lookup table, followed by
// cases that must not be converted to one. Each output is compared against an
// equivalent reference computed without a case statement, so the reference itself is
// never tabled. Selectors are wide enough, with enough distinct values, that the
// branch lowering they replace is deep enough to make a table worthwhile.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 1'b0;
  always #5 clk = ~clk;

  logic [31:0] cyc = 0;

  // Accept A: single output, blocking assignment, all selector values covered.
  logic [15:0] accept_a_out, accept_a_ref;
  always_comb
    case (cyc[3:0])
      4'd0: accept_a_out = 16'h1111;
      4'd1: accept_a_out = 16'h2222;
      4'd2: accept_a_out = 16'h4444;
      4'd3: accept_a_out = 16'h8888;
      default: accept_a_out = 16'h0f0f;
    endcase
  assign accept_a_ref = (cyc[3:0] == 4'd0) ? 16'h1111
                      : (cyc[3:0] == 4'd1) ? 16'h2222
                      : (cyc[3:0] == 4'd2) ? 16'h4444
                      : (cyc[3:0] == 4'd3) ? 16'h8888 : 16'h0f0f;

  // Accept B: single output, non-blocking assignment, with a default value set before
  //         the case and not all selector values covered.
  logic [15:0] accept_b_out, accept_b_ref;
  // verilator lint_off CASEINCOMPLETE
  always_ff @(posedge clk) begin
    accept_b_out <= 16'hffff;
    case (cyc[3:0])
      4'd0: accept_b_out <= 16'h0001;
      4'd1: accept_b_out <= 16'h0002;
      4'd2: accept_b_out <= 16'h0004;
      4'd3: accept_b_out <= 16'h0008;
    endcase
  end
  // verilator lint_on CASEINCOMPLETE
  always_ff @(posedge clk)
    accept_b_ref <= (cyc[3:0] == 4'd0) ? 16'h0001
                  : (cyc[3:0] == 4'd1) ? 16'h0002
                  : (cyc[3:0] == 4'd2) ? 16'h0004
                  : (cyc[3:0] == 4'd3) ? 16'h0008 : 16'hffff;

  // Accept C: three outputs, blocking assignment, with a default branch.
  logic [11:0] accept_c_out_0, accept_c_ref_0;
  logic [11:0] accept_c_out_1, accept_c_ref_1;
  logic [11:0] accept_c_out_2, accept_c_ref_2;
  always_comb
    case (cyc[3:0])
      4'd0: begin
        accept_c_out_0 = 12'h001;
        accept_c_out_1 = 12'h010;
        accept_c_out_2 = 12'h100;
      end
      4'd1: begin
        accept_c_out_0 = 12'h002;
        accept_c_out_1 = 12'h020;
        accept_c_out_2 = 12'h200;
      end
      4'd2: begin
        accept_c_out_0 = 12'h004;
        accept_c_out_1 = 12'h040;
        accept_c_out_2 = 12'h400;
      end
      4'd3: begin
        accept_c_out_0 = 12'h008;
        accept_c_out_1 = 12'h080;
        accept_c_out_2 = 12'h800;
      end
      default: begin
        accept_c_out_0 = 12'h000;
        accept_c_out_1 = 12'h0ff;
        accept_c_out_2 = 12'hfff;
      end
    endcase
  assign accept_c_ref_0 = (cyc[3:0] == 4'd0) ? 12'h001 : (cyc[3:0] == 4'd1) ? 12'h002
                        : (cyc[3:0] == 4'd2) ? 12'h004 : (cyc[3:0] == 4'd3) ? 12'h008 : 12'h000;
  assign accept_c_ref_1 = (cyc[3:0] == 4'd0) ? 12'h010 : (cyc[3:0] == 4'd1) ? 12'h020
                        : (cyc[3:0] == 4'd2) ? 12'h040 : (cyc[3:0] == 4'd3) ? 12'h080 : 12'h0ff;
  assign accept_c_ref_2 = (cyc[3:0] == 4'd0) ? 12'h100 : (cyc[3:0] == 4'd1) ? 12'h200
                        : (cyc[3:0] == 4'd2) ? 12'h400 : (cyc[3:0] == 4'd3) ? 12'h800 : 12'hfff;

  // Accept D: two outputs, non-blocking assignment, empty default branch, with default
  //         values set before the case.
  logic [15:0] accept_d_out_0, accept_d_ref_0;
  logic [15:0] accept_d_out_1, accept_d_ref_1;
  always_ff @(posedge clk) begin
    accept_d_out_0 <= 16'h0000;
    accept_d_out_1 <= 16'hffff;
    case (cyc[3:0])
      4'd0: begin
        accept_d_out_0 <= 16'h0001;
        accept_d_out_1 <= 16'h0010;
      end
      4'd1: begin
        accept_d_out_0 <= 16'h0002;
        accept_d_out_1 <= 16'h0020;
      end
      4'd2: begin
        accept_d_out_0 <= 16'h0004;
        accept_d_out_1 <= 16'h0040;
      end
      4'd3: begin
        accept_d_out_0 <= 16'h0008;
        accept_d_out_1 <= 16'h0080;
      end
      default: begin
      end
    endcase
  end
  always_ff @(posedge clk) begin
    accept_d_ref_0 <= (cyc[3:0] == 4'd0) ? 16'h0001 : (cyc[3:0] == 4'd1) ? 16'h0002
                    : (cyc[3:0] == 4'd2) ? 16'h0004 : (cyc[3:0] == 4'd3) ? 16'h0008 : 16'h0000;
    accept_d_ref_1 <= (cyc[3:0] == 4'd0) ? 16'h0010 : (cyc[3:0] == 4'd1) ? 16'h0020
                    : (cyc[3:0] == 4'd2) ? 16'h0040 : (cyc[3:0] == 4'd3) ? 16'h0080 : 16'hffff;
  end

  // Accept E: casez with don't-care bits.
  logic [15:0] accept_e_out, accept_e_ref;
  always_comb
    casez (cyc[3:0])
      4'b00??: accept_e_out = 16'haaaa;
      4'b01??: accept_e_out = 16'hbbbb;
      4'b10??: accept_e_out = 16'hcccc;
      4'b11??: accept_e_out = 16'hdddd;
    endcase
  assign accept_e_ref = (cyc[3:2] == 2'd0) ? 16'haaaa : (cyc[3:2] == 2'd1) ? 16'hbbbb
                      : (cyc[3:2] == 2'd2) ? 16'hcccc : 16'hdddd;

  // Accept F: an item that can never match, and an item listing multiple values.
  logic [15:0] accept_f_out, accept_f_ref;
  // verilator lint_off CASEWITHX
  always_comb
    casez (cyc[3:0])
      4'bxxx0: accept_f_out = 16'h0000;  // X can never match in 2-state
      4'b0001, 4'b0011, 4'b0101: accept_f_out = 16'h5555;  // lists three values
      default: accept_f_out = 16'h9999;
    endcase
  // verilator lint_on CASEWITHX
  assign accept_f_ref = (cyc[3:0] == 4'd1 || cyc[3:0] == 4'd3 || cyc[3:0] == 4'd5)
                      ? 16'h5555 : 16'h9999;

  // Accept G: items assign different subsets of two outputs, with default values (and an
  //         unrelated output) set before the case.
  logic [15:0] accept_g_out_0, accept_g_ref_0;
  logic [15:0] accept_g_out_1, accept_g_ref_1;
  logic [15:0] accept_g_out_2, accept_g_ref_2;
  always_comb begin
    accept_g_out_0 = 16'h0000;
    accept_g_out_1 = 16'hffff;
    accept_g_out_2 = 16'h3333;  // not assigned in the case
    case (cyc[3:0])
      4'd0: accept_g_out_0 = 16'h0001;
      4'd1: accept_g_out_1 = 16'h0002;
      4'd2: begin
        accept_g_out_0 = 16'h0004;
        accept_g_out_1 = 16'h0008;
      end
      4'd3: accept_g_out_0 = 16'h0010;
      default: ;
    endcase
  end
  assign accept_g_ref_0 = (cyc[3:0] == 4'd0) ? 16'h0001 : (cyc[3:0] == 4'd2) ? 16'h0004
                        : (cyc[3:0] == 4'd3) ? 16'h0010 : 16'h0000;
  assign accept_g_ref_1 = (cyc[3:0] == 4'd1) ? 16'h0002 : (cyc[3:0] == 4'd2) ? 16'h0008 : 16'hffff;
  assign accept_g_ref_2 = 16'h3333;

  // Accept H: unique0 enum case; the selector may hold an out-of-range value.
  typedef enum logic [3:0] {
    NE0,
    NE1,
    NE2,
    NE3,
    NE4
  } ne_t;
  ne_t accept_h_in;
  assign accept_h_in = ne_t'(cyc[3:0]);
  logic [15:0] accept_h_out, accept_h_ref;
  always_comb begin
    accept_h_out = 16'hffff;
    unique0 case (accept_h_in)
      NE0: accept_h_out = 16'h0001;
      NE1: accept_h_out = 16'h0002;
      NE2: accept_h_out = 16'h0003;
      NE3: accept_h_out = 16'h0004;
      NE4: accept_h_out = 16'h0005;
    endcase
  end
  assign accept_h_ref = (cyc[3:0] == 4'd0) ? 16'h0001 : (cyc[3:0] == 4'd1) ? 16'h0002
                      : (cyc[3:0] == 4'd2) ? 16'h0003 : (cyc[3:0] == 4'd3) ? 16'h0004
                      : (cyc[3:0] == 4'd4) ? 16'h0005 : 16'hffff;

  // The cases below are intentionally NOT converted to a lookup table.

  // Reject A: too few distinct values, so the branch lowering is cheaper than a load.
  logic [15:0] reject_a_out, reject_a_ref;
  always_comb
    case (cyc[3:0])
      4'd0: reject_a_out = 16'h0001;
      4'd1: reject_a_out = 16'h0002;
      default: reject_a_out = 16'h00ff;
    endcase
  assign reject_a_ref = (cyc[3:0] == 4'd0) ? 16'h0001 : (cyc[3:0] == 4'd1) ? 16'h0002 : 16'h00ff;

  // Reject B: a one-bit selector, too shallow to be worth a load.
  logic [19:0] reject_b_out, reject_b_ref;
  always_comb
    case (cyc[0])
      1'b0: reject_b_out = 20'h00001;
      1'b1: reject_b_out = 20'h00002;
      default: reject_b_out = 20'h00000;
    endcase
  assign reject_b_ref = cyc[0] ? 20'h00002 : 20'h00001;

  // Reject C: a 12-bit selector, too wide to table.
  logic [15:0] reject_c_out, reject_c_ref;
  always_comb
    case (cyc[11:0])
      12'd0: reject_c_out = 16'h0001;
      12'd1: reject_c_out = 16'h0002;
      12'd2: reject_c_out = 16'h0004;
      default: reject_c_out = 16'h0000;
    endcase
  assign reject_c_ref = (cyc[11:0] == 12'd0) ? 16'h0001
                      : (cyc[11:0] == 12'd1) ? 16'h0002
                      : (cyc[11:0] == 12'd2) ? 16'h0004 : 16'h0000;

  // Reject D: a 17-bit selector, too wide to table.
  logic [16:0] reject_d_in;
  assign reject_d_in = cyc[16:0];
  logic [15:0] reject_d_out, reject_d_ref;
  // verilator lint_off CASEINCOMPLETE
  always_comb begin
    reject_d_out = 16'hbeef;
    case (reject_d_in)
      17'd0: reject_d_out = 16'h0001;
      17'd1: reject_d_out = 16'h0002;
      17'd2: reject_d_out = 16'h0004;
    endcase
  end
  // verilator lint_on CASEINCOMPLETE
  assign reject_d_ref = (reject_d_in == 17'd0) ? 16'h0001
                      : (reject_d_in == 17'd1) ? 16'h0002
                      : (reject_d_in == 17'd2) ? 16'h0004 : 16'hbeef;

  // Reject E: a whole output and a sub-range of it assigned in different items.
  logic [7:0] reject_e_out, reject_e_ref;
  always_comb begin
    reject_e_out = 8'h00;
    reject_e_out[3:0] = 4'h0;
    case (cyc[1:0])
      2'b00: reject_e_out = 8'haa;  // assigns the whole output
      2'b01: reject_e_out[3:0] = 4'h5;  // assigns a sub-range of the same output
      default: ;
    endcase
  end
  assign reject_e_ref = (cyc[1:0] == 2'd0) ? 8'haa : (cyc[1:0] == 2'd1) ? 8'h05 : 8'h00;

  // Reject F: a sub-range's default value is overwritten by a later whole-output default
  //         before the case, so the sub-range's pre-case value is set elsewhere.
  logic [31:0] reject_f_out, reject_f_ref;
  always_comb begin
    reject_f_out[15:0] = 16'h0005;  // farther default for the sub-range
    reject_f_out = 32'h0;  // closer whole-output default overwrites the sub-range to 0
    case (cyc[1:0])
      2'b00: reject_f_out[15:0] = 16'habcd;  // only the sub-range is assigned in the case
      default: ;
    endcase
  end
  assign reject_f_ref = (cyc[1:0] == 2'd0) ? 32'h0000abcd : 32'h00000000;

  // Test driver/checker
  always @(posedge clk) begin
    `checkh(accept_a_out, accept_a_ref);
    `checkh(accept_b_out, accept_b_ref);
    `checkh(accept_c_out_0, accept_c_ref_0);
    `checkh(accept_c_out_1, accept_c_ref_1);
    `checkh(accept_c_out_2, accept_c_ref_2);
    `checkh(accept_d_out_0, accept_d_ref_0);
    `checkh(accept_d_out_1, accept_d_ref_1);
    `checkh(accept_e_out, accept_e_ref);
    `checkh(accept_f_out, accept_f_ref);
    `checkh(accept_g_out_0, accept_g_ref_0);
    `checkh(accept_g_out_1, accept_g_ref_1);
    `checkh(accept_g_out_2, accept_g_ref_2);
    `checkh(accept_h_out, accept_h_ref);
    `checkh(reject_a_out, reject_a_ref);
    `checkh(reject_b_out, reject_b_ref);
    `checkh(reject_c_out, reject_c_ref);
    `checkh(reject_d_out, reject_d_ref);
    `checkh(reject_e_out, reject_e_ref);
    `checkh(reject_f_out, reject_f_ref);

    cyc <= cyc + 32'd1;
    if (cyc == 32'd32) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
