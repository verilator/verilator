// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

module t (
  input logic clk
);

  localparam int INSTS = 8;
  localparam int SAMPLE_BITS = INSTS * (64 + 16 + 1);

  int cyc;
  logic rst_n;
  logic [31:0] stim_a;
  logic [31:0] stim_b;
  logic [31:0] crc;

  logic [INSTS-1:0] valid_i;
  logic [INSTS-1:0][31:0] data_i;
  logic [INSTS-1:0][15:0] tweak_i;
  logic [INSTS-1:0][1:0] mode_i;
  logic [INSTS-1:0][63:0] y_o;
  logic [INSTS-1:0][15:0] tag_o;
  logic [INSTS-1:0] valid_o;
  logic [SAMPLE_BITS-1:0] sample;

  function automatic logic [31:0] lfsr32(input logic [31:0] s);
    lfsr32 = {s[30:0], s[31] ^ s[21] ^ s[1] ^ s[0]};
  endfunction

  function automatic logic [31:0] crc32_bits(
    input logic [31:0] crc_i,
    input logic [SAMPLE_BITS-1:0] data
  );
    logic [31:0] c;
    c = crc_i;
    for (int i = 0; i < SAMPLE_BITS; i++) begin
      logic feedback;
      feedback = c[31] ^ data[i];
      c = {c[30:0], 1'b0};
      if (feedback) c ^= 32'h04c11db7;
    end
    return c;
  endfunction

  generate
    for (genvar g = 0; g < INSTS; g++) begin : gen_stim
      localparam logic [31:0] K32 = 32'h9e37_79b9 ^ (32'h1020_4081 * (g + 1));
      localparam logic [15:0] K16 = 16'h5a3c ^ (16'h2113 * (g + 3));

      assign valid_i[g] = rst_n && (((cyc + g) % 5) != 1) && (((cyc ^ g) & 3) != 2);
      assign data_i[g] = (stim_a ^ {K16, 16'(cyc * (g + 7))})
                         + {stim_b[15:0], stim_b[31:16]}
                         + K32
                         + (32'((cyc + 1) * (g + 5)) ^ {8'(g), 8'(g * 9), 8'(cyc), 8'(cyc >> 1)});
      assign tweak_i[g] = stim_b[15:0] ^ K16 ^ 16'(cyc + (g * 11))
                          ^ {4'(g), 4'(cyc), 4'(g ^ cyc), 4'((cyc >> 2) + g)};
      assign mode_i[g] = 2'((cyc >> (g % 3)) + g);
      assign sample[(g*(64+16+1)) +: (64+16+1)] = {valid_o[g], tag_o[g], y_o[g]};
    end
  endgenerate

  sg_mix_core #(
    .P_SEED_A(32'h6a09_e667), .P_SEED_B(32'hbb67_ae85), .P_SEED_C(32'h3c6e_f372),
    .P_SEED_D(32'ha54f_f53a), .P_SEED_ACC(32'h510e_527f), .P_ROUND_INC(8'h1d),
    .P_IDLE_XOR(32'h0bad_f00d), .P_ROT_A(9), .P_ROT_B(3), .P_ROT_C(15), .P_ROT_D(19)
  ) i_core0 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[0]), .data_i(data_i[0]), .tweak_i(tweak_i[0]),
    .mode_i(mode_i[0]), .y_o(y_o[0]), .tag_o(tag_o[0]), .valid_o(valid_o[0])
  );

  sg_mix_core #(
    .P_SEED_A(32'h6a09_e667), .P_SEED_B(32'hbb67_ae85), .P_SEED_C(32'h3c6e_f372),
    .P_SEED_D(32'ha54f_f53a), .P_SEED_ACC(32'h510e_527f), .P_ROUND_INC(8'h1d),
    .P_IDLE_XOR(32'h0bad_f00d), .P_ROT_A(9), .P_ROT_B(3), .P_ROT_C(15), .P_ROT_D(19)
  ) i_core1 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[1]), .data_i(data_i[1]), .tweak_i(tweak_i[1]),
    .mode_i(mode_i[1]), .y_o(y_o[1]), .tag_o(tag_o[1]), .valid_o(valid_o[1])
  );

  sg_mix_core #(
    .P_SEED_A(32'h1319_8a2e), .P_SEED_B(32'h0370_7344), .P_SEED_C(32'ha409_3822),
    .P_SEED_D(32'h299f_31d0), .P_SEED_ACC(32'h082e_fa98), .P_ROUND_INC(8'h27),
    .P_IDLE_XOR(32'hc001_cafe), .P_ROT_A(5), .P_ROT_B(7), .P_ROT_C(11), .P_ROT_D(23)
  ) i_core2 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[2]), .data_i(data_i[2]), .tweak_i(tweak_i[2]),
    .mode_i(mode_i[2]), .y_o(y_o[2]), .tag_o(tag_o[2]), .valid_o(valid_o[2])
  );

  sg_mix_core #(
    .P_SEED_A(32'h1319_8a2e), .P_SEED_B(32'h0370_7344), .P_SEED_C(32'ha409_3822),
    .P_SEED_D(32'h299f_31d0), .P_SEED_ACC(32'h082e_fa98), .P_ROUND_INC(8'h27),
    .P_IDLE_XOR(32'hc001_cafe), .P_ROT_A(5), .P_ROT_B(7), .P_ROT_C(11), .P_ROT_D(23)
  ) i_core3 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[3]), .data_i(data_i[3]), .tweak_i(tweak_i[3]),
    .mode_i(mode_i[3]), .y_o(y_o[3]), .tag_o(tag_o[3]), .valid_o(valid_o[3])
  );

  sg_mix_core #(
    .P_SEED_A(32'h243f_6a88), .P_SEED_B(32'h85a3_08d3), .P_SEED_C(32'h1319_8a2e),
    .P_SEED_D(32'h0370_7344), .P_SEED_ACC(32'ha409_3822), .P_ROUND_INC(8'h33),
    .P_IDLE_XOR(32'h5bd1_e995), .P_ROT_A(13), .P_ROT_B(5), .P_ROT_C(17), .P_ROT_D(29)
  ) i_core4 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[4]), .data_i(data_i[4]), .tweak_i(tweak_i[4]),
    .mode_i(mode_i[4]), .y_o(y_o[4]), .tag_o(tag_o[4]), .valid_o(valid_o[4])
  );

  sg_mix_core #(
    .P_SEED_A(32'h243f_6a88), .P_SEED_B(32'h85a3_08d3), .P_SEED_C(32'h1319_8a2e),
    .P_SEED_D(32'h0370_7344), .P_SEED_ACC(32'ha409_3822), .P_ROUND_INC(8'h33),
    .P_IDLE_XOR(32'h5bd1_e995), .P_ROT_A(13), .P_ROT_B(5), .P_ROT_C(17), .P_ROT_D(29)
  ) i_core5 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[5]), .data_i(data_i[5]), .tweak_i(tweak_i[5]),
    .mode_i(mode_i[5]), .y_o(y_o[5]), .tag_o(tag_o[5]), .valid_o(valid_o[5])
  );

  sg_mix_core #(
    .P_SEED_A(32'h0f1e_2d3c), .P_SEED_B(32'h4b5a_6978), .P_SEED_C(32'h89ab_cdef),
    .P_SEED_D(32'h1021_3243), .P_SEED_ACC(32'h5465_7687), .P_ROUND_INC(8'h3f),
    .P_IDLE_XOR(32'hdead_beef), .P_ROT_A(3), .P_ROT_B(11), .P_ROT_C(21), .P_ROT_D(27)
  ) i_core6 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[6]), .data_i(data_i[6]), .tweak_i(tweak_i[6]),
    .mode_i(mode_i[6]), .y_o(y_o[6]), .tag_o(tag_o[6]), .valid_o(valid_o[6])
  );

  sg_mix_core #(
    .P_SEED_A(32'h55aa_963c), .P_SEED_B(32'h33cc_f00d), .P_SEED_C(32'hcafe_babe),
    .P_SEED_D(32'h7654_3210), .P_SEED_ACC(32'hfedc_ba98), .P_ROUND_INC(8'h49),
    .P_IDLE_XOR(32'h1ce0_1ce0), .P_ROT_A(15), .P_ROT_B(9), .P_ROT_C(25), .P_ROT_D(31)
  ) i_core7 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[7]), .data_i(data_i[7]), .tweak_i(tweak_i[7]),
    .mode_i(mode_i[7]), .y_o(y_o[7]), .tag_o(tag_o[7]), .valid_o(valid_o[7])
  );

  initial begin
    cyc = 0;
    rst_n = 1'b0;
    stim_a = 32'h243f_6a88;
    stim_b = 32'h85a3_08d3;
    crc = 32'hffff_ffff;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    rst_n <= (cyc >= 3);
    stim_a <= lfsr32(stim_a) ^ {stim_b[7:0], stim_b[31:8]} ^ 32'(cyc * 17);
    stim_b <= lfsr32(stim_b ^ 32'hc001_cafe) + {stim_a[15:0], stim_a[31:16]};

    if (cyc > 9) crc <= crc32_bits(crc, sample);

    if (cyc == 180) begin
      $write("crc=%08x\n", crc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_mix_core #(
  parameter logic [31:0] P_SEED_A = 32'h6a09_e667,
  parameter logic [31:0] P_SEED_B = 32'hbb67_ae85,
  parameter logic [31:0] P_SEED_C = 32'h3c6e_f372,
  parameter logic [31:0] P_SEED_D = 32'ha54f_f53a,
  parameter logic [31:0] P_SEED_ACC = 32'h510e_527f,
  parameter logic [7:0]  P_ROUND_INC = 8'h1d,
  parameter logic [31:0] P_IDLE_XOR = 32'h0bad_f00d,
  parameter int unsigned P_ROT_A = 9,
  parameter int unsigned P_ROT_B = 3,
  parameter int unsigned P_ROT_C = 15,
  parameter int unsigned P_ROT_D = 19
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic [31:0] data_i,
  input  logic [15:0] tweak_i,
  input  logic [1:0]  mode_i,
  output logic [63:0] y_o,
  output logic [15:0] tag_o,
  output logic        valid_o
); /*verilator subgraph_boundary*/

  sg_mix_pipe #(
    .P_ROT_A(P_ROT_A),
    .P_ROT_B(P_ROT_B),
    .P_ROT_C(P_ROT_C),
    .P_ROT_D(P_ROT_D)
  ) i_pipe (
    .clk(clk),
    .rst_n(rst_n),
    .valid_i(valid_i),
    .data_i(data_i),
    .tweak_i(tweak_i),
    .mode_i(mode_i),
    .y_o(y_o),
    .tag_o(tag_o),
    .valid_o(valid_o),
    .seed_a_i(P_SEED_A),
    .seed_b_i(P_SEED_B),
    .seed_c_i(P_SEED_C),
    .seed_d_i(P_SEED_D),
    .seed_acc_i(P_SEED_ACC),
    .round_inc_i(P_ROUND_INC),
    .idle_xor_i(P_IDLE_XOR)
  );

endmodule

module sg_mix_pipe #(
  parameter int unsigned P_ROT_A = 9,
  parameter int unsigned P_ROT_B = 3,
  parameter int unsigned P_ROT_C = 15,
  parameter int unsigned P_ROT_D = 19
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic [31:0] data_i,
  input  logic [15:0] tweak_i,
  input  logic [1:0]  mode_i,
  output logic [63:0] y_o,
  output logic [15:0] tag_o,
  output logic        valid_o,
  input  logic [31:0] seed_a_i,
  input  logic [31:0] seed_b_i,
  input  logic [31:0] seed_c_i,
  input  logic [31:0] seed_d_i,
  input  logic [31:0] seed_acc_i,
  input  logic [7:0]  round_inc_i,
  input  logic [31:0] idle_xor_i
);

  logic [31:0] a_q;
  logic [31:0] b_q;
  logic [31:0] c_q;
  logic [31:0] d_q;
  logic [31:0] acc_q;
  logic [31:0] data_q;
  logic [15:0] tweak_q;
  logic [1:0] mode_q;
  logic [7:0] round_q;
  logic [2:0] valid_pipe_q;
  logic [15:0] sbox_word;
  logic [31:0] permuted;
  logic [31:0] folded_base;
  logic [31:0] folded;

  sg_sbox4 i_sbox0 (.nibble(a_q[3:0] ^ round_q[3:0]), .out(sbox_word[3:0]));
  sg_sbox4 i_sbox1 (.nibble(b_q[7:4] ^ round_q[3:0]), .out(sbox_word[7:4]));
  sg_sbox4 i_sbox2 (.nibble(c_q[11:8] ^ round_q[3:0]), .out(sbox_word[11:8]));
  sg_sbox4 i_sbox3 (.nibble(d_q[15:12] ^ round_q[3:0]), .out(sbox_word[15:12]));

  function automatic logic [31:0] rotl32(input logic [31:0] x, input int sh);
    rotl32 = (x << sh) | (x >> (32 - sh));
  endfunction

  function automatic logic [31:0] mode_mix(
    input logic [31:0] x,
    input logic [31:0] y,
    input logic [1:0] mode
  );
    unique case (mode)
      2'd0: mode_mix = rotl32(x + y, 5) ^ (x & 32'h0f0f_f0f0);
      2'd1: mode_mix = rotl32(x ^ y, 11) + (y | 32'h1357_9bdf);
      2'd2: mode_mix = rotl32(x - y, 17) ^ {x[15:0], y[31:16]};
      default: mode_mix = rotl32(x + {y[7:0], y[31:8]}, 23) + (x ^ 32'ha5a5_3c3c);
    endcase
  endfunction

  always_comb begin
    permuted = {sbox_word, sbox_word ^ a_q[31:16]} ^ rotl32(b_q, 7) ^ rotl32(c_q, 13);
    folded_base = mode_mix(permuted ^ acc_q, d_q + {16'h0, tweak_q}, mode_q);
    folded = folded_base;
    for (int i = 0; i < 4; i++) begin
      folded[(i*8) +: 8] = folded_base[(i*8) +: 8]
                            ^ (folded_base[((3-i)*8) +: 8] + (8'(round_q) ^ 8'(i * 8'h31)));
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      a_q <= seed_a_i;
      b_q <= seed_b_i;
      c_q <= seed_c_i;
      d_q <= seed_d_i;
      acc_q <= seed_acc_i;
      data_q <= 32'h0;
      tweak_q <= 16'h0;
      mode_q <= 2'h0;
      round_q <= 8'h00;
      valid_pipe_q <= 3'b000;
      y_o <= 64'h0;
      tag_o <= 16'h0;
      valid_o <= 1'b0;
    end else begin
      data_q <= data_i;
      tweak_q <= tweak_i;
      mode_q <= mode_i;
      valid_pipe_q <= {valid_pipe_q[1:0], valid_i};
      round_q <= round_q + round_inc_i + {7'b0, valid_pipe_q[0]};

      if (valid_pipe_q[0]) begin
        a_q <= mode_mix(data_q ^ a_q, b_q + {tweak_q, tweak_q}, mode_q);
        b_q <= rotl32(b_q + folded + 32'h9e37_79b9, P_ROT_B);
        c_q <= mode_mix(c_q ^ {tweak_q, data_q[15:0]}, data_q + d_q, mode_q + 2'd1);
        d_q <= rotl32(d_q ^ folded ^ data_q, P_ROT_D) + {24'h0, round_q};
        acc_q <= acc_q + folded + (a_q ^ c_q) + 32'(valid_pipe_q);
      end else begin
        a_q <= rotl32(a_q ^ 32'h1f12_bb5a, P_ROT_A);
        b_q <= b_q + 32'h0101_0001 + {16'h0, tweak_q};
        c_q <= rotl32(c_q + acc_q, P_ROT_C);
        d_q <= d_q ^ rotl32(acc_q, 21);
        acc_q <= acc_q ^ folded ^ idle_xor_i;
      end

      y_o <= {folded ^ a_q ^ c_q, acc_q + b_q + d_q};
      tag_o <= sbox_word ^ acc_q[15:0] ^ acc_q[31:16] ^ {8'h0, round_q};
      valid_o <= valid_pipe_q[2];
    end
  end

endmodule

module sg_sbox4 (
  input  logic [3:0] nibble,
  output logic [3:0] out
);

  always_comb begin
    unique case (nibble)
      4'h0: out = 4'hc;
      4'h1: out = 4'h5;
      4'h2: out = 4'h6;
      4'h3: out = 4'hb;
      4'h4: out = 4'h9;
      4'h5: out = 4'h0;
      4'h6: out = 4'ha;
      4'h7: out = 4'hd;
      4'h8: out = 4'h3;
      4'h9: out = 4'he;
      4'ha: out = 4'hf;
      4'hb: out = 4'h8;
      4'hc: out = 4'h4;
      4'hd: out = 4'h7;
      4'he: out = 4'h1;
      default: out = 4'h2;
    endcase
  end

endmodule
