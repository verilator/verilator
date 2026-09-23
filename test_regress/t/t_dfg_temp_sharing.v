// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module temp_leaf #(
    parameter W = 7
) (
    input clk_i,
    input [W-1:0] a_i,
    b_i,
    c_i,
    d_i,
    output [W-1:0] comb0_o,
    comb1_o,
    output logic [W-1:0] state_o = 0
);
  /* verilator no_inline_module */
  typedef logic [W-1:0] word_t;
  word_t a_r = 0, b_r = 0, c_r = 0, d_r = 0;
  always_ff @(posedge clk_i) begin
    a_r <= a_i;
    b_r <= b_i;
    c_r <= c_i;
    d_r <= d_i;
  end
  // Two live intermediates of the same type must occupy distinct slots.
  assign comb0_o = ((a_r + b_r) ^ c_r) + ((a_r + b_r) & d_r);
  assign comb1_o = ((a_r ^ b_r) + c_r) ^ ((a_r ^ b_r) | d_r);
  always_ff @(negedge clk_i) state_o <= (a_r + b_r) ^ (state_o + c_r);
endmodule

module t;
  for (genvar n = 0; n < 16; ++n) begin : g
    localparam W = (n % 4 == 0) ? 7 : (n % 4 == 1) ? 33 : (n % 4 == 2) ? 65 : 95;
    typedef logic [W-1:0] word_t;
    bit clk = 0;
    word_t a = 0, b = 0, c = 0, d = 0;
    wire [W-1:0] comb0, comb1, state_value;
    temp_leaf #(
        .W(W)
    ) leaf (
        .clk_i(clk),
        .a_i(a),
        .b_i(b),
        .c_i(c),
        .d_i(d),
        .comb0_o(comb0),
        .comb1_o(comb1),
        .state_o(state_value)
    );
    initial begin
      automatic word_t expected0 = 0, expected1 = 0, expected_state = 0;
      word_t sum, xored;
      for (int cycle = 0; cycle < 200; ++cycle) begin
        a = W'({$random, $random, $random});
        b = W'({$random, $random, $random});
        c = W'({$random, $random, $random});
        d = W'({$random, $random, $random});
        #1;
        `checkh(comb0, expected0);
        `checkh(comb1, expected1);
        `checkh(state_value, expected_state);
        clk = 1;
        sum = a + b;
        xored = a ^ b;
        expected0 = (sum ^ c) + (sum & d);
        expected1 = (xored + c) ^ (xored | d);
        #1;
        `checkh(comb0, expected0);
        `checkh(comb1, expected1);
        `checkh(state_value, expected_state);
        clk = 0;
        expected_state = sum ^ (expected_state + c);
        #1;
        `checkh(comb0, expected0);
        `checkh(comb1, expected1);
        `checkh(state_value, expected_state);
      end
    end
  end
  initial begin
    #601;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
