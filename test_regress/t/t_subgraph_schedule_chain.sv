// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

module t (
  input logic clk
);

  localparam int N_SRC = 6;
  localparam int N_CLUSTER = 2;
  localparam int N_TOP_DST = 2;
  localparam int N_TOTAL = N_SRC + N_CLUSTER + N_TOP_DST;
  localparam int SAMPLE_BITS = N_TOTAL * (64 + 16 + 1);

  int cyc;
  logic rst_n;
  logic [63:0] stim_a;
  logic [63:0] stim_b;
  logic [31:0] stim_c;
  logic [31:0] crc;

  logic [N_SRC-1:0] src_valid_i;
  logic [N_SRC-1:0] src_hold_i;
  logic [N_SRC-1:0][63:0] src_data_i;
  logic [N_SRC-1:0][15:0] src_cfg_i;
  logic [N_SRC-1:0][7:0] src_seed_i;
  logic [N_SRC-1:0][63:0] src_y_o;
  logic [N_SRC-1:0][15:0] src_meta_o;
  logic [N_SRC-1:0] src_valid_o;

  logic [N_TOP_DST-1:0] top_dst_valid_i;
  logic [N_TOP_DST-1:0] top_dst_hold_i;
  logic [N_TOP_DST-1:0][63:0] top_dst_data_i;
  logic [N_TOP_DST-1:0][15:0] top_dst_cfg_i;
  logic [N_TOP_DST-1:0][7:0] top_dst_seed_i;
  logic [N_TOP_DST-1:0][63:0] top_dst_y_o;
  logic [N_TOP_DST-1:0][15:0] top_dst_meta_o;
  logic [N_TOP_DST-1:0] top_dst_valid_o;

  logic [N_CLUSTER-1:0] cluster_in_valid_i;
  logic [N_CLUSTER-1:0] cluster_in_hold_i;
  logic [N_CLUSTER-1:0][63:0] cluster_in_data_i;
  logic [N_CLUSTER-1:0][15:0] cluster_in_cfg_i;
  logic [N_CLUSTER-1:0][7:0] cluster_in_seed_i;
  logic [N_CLUSTER-1:0][63:0] cluster_y_o;
  logic [N_CLUSTER-1:0][15:0] cluster_meta_o;
  logic [N_CLUSTER-1:0] cluster_valid_o;

  logic [SAMPLE_BITS-1:0] sample;

  function automatic logic [63:0] lfsr64(input logic [63:0] s);
    lfsr64 = {s[62:0], s[63] ^ s[62] ^ s[60] ^ s[59]};
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
    for (genvar g = 0; g < N_SRC; g++) begin : gen_src_stim
      localparam logic [63:0] K64 = 64'h9e37_79b9_7f4a_7c15 ^ (64'h0102_0408_1020_4081 * (g + 1));
      localparam logic [15:0] K16 = 16'h41c6 ^ (16'h1357 * (g + 5));

      assign src_valid_i[g] = rst_n && (((cyc + g) % 6) != 2) && (((cyc ^ (g * 3)) & 4) == 0);
      assign src_hold_i[g] = (((cyc + (g * 5)) & 7) == 3);
      assign src_data_i[g] = stim_a
                             ^ {stim_c, ~stim_c}
                             ^ {K16, K16, K16, K16}
                             ^ K64
                             ^ ((64'(cyc) + 64'd3) * 64'(g + 9) << (g % 11));
      assign src_cfg_i[g] = stim_b[15:0] ^ K16 ^ 16'(cyc * (g + 1));
      assign src_seed_i[g] = 8'((cyc << (g % 2)) ^ (g * 8'h1d) ^ stim_a[7:0]);
      assign sample[(g*(64+16+1)) +: (64+16+1)] = {src_valid_o[g], src_meta_o[g], src_y_o[g]};
    end
  endgenerate

  assign top_dst_valid_i[0] = rst_n && src_valid_o[0] && src_valid_o[2] && !src_hold_i[4];
  assign top_dst_hold_i[0] = ((cyc + 5) & 7) == 1;
  assign top_dst_data_i[0] = src_y_o[0] ^ {src_meta_o[2], src_y_o[2][47:0]} ^ {stim_c, stim_b[31:0]};
  assign top_dst_cfg_i[0] = src_meta_o[0] ^ src_meta_o[2] ^ 16'h44aa;
  assign top_dst_seed_i[0] = src_seed_i[0] ^ src_seed_i[2] ^ 8'h91;

  assign top_dst_valid_i[1] = rst_n && src_valid_o[1] && src_valid_o[5] && !cluster_valid_o[0];
  assign top_dst_hold_i[1] = ((cyc + 2) & 7) == 6;
  assign top_dst_data_i[1] = src_y_o[1] + {src_meta_o[5], src_y_o[5][47:0]} + {stim_b[31:0], stim_c};
  assign top_dst_cfg_i[1] = src_meta_o[1] + src_meta_o[5] + 16'h0f0f;
  assign top_dst_seed_i[1] = src_seed_i[1] + src_seed_i[5] + 8'h2b;

  assign cluster_in_valid_i[0] = rst_n && src_valid_o[3] && src_valid_o[4];
  assign cluster_in_hold_i[0] = ((cyc + 1) & 3) == 2;
  assign cluster_in_data_i[0] = src_y_o[3] ^ {src_meta_o[4], src_y_o[4][47:0]} ^ stim_a;
  assign cluster_in_cfg_i[0] = src_meta_o[3] ^ src_meta_o[4] ^ 16'h55aa;
  assign cluster_in_seed_i[0] = src_seed_i[3] ^ src_seed_i[4] ^ 8'hc3;

  assign cluster_in_valid_i[1] = rst_n && src_valid_o[2] && src_valid_o[5];
  assign cluster_in_hold_i[1] = ((cyc + 6) & 7) == 4;
  assign cluster_in_data_i[1] = src_y_o[2] + {src_meta_o[5], src_y_o[5][47:0]} + stim_b;
  assign cluster_in_cfg_i[1] = src_meta_o[2] + src_meta_o[5] + 16'h33cc;
  assign cluster_in_seed_i[1] = src_seed_i[2] + src_seed_i[5] + 8'h17;

  assign sample[((N_SRC+0)*(64+16+1)) +: (64+16+1)] = {top_dst_valid_o[0], top_dst_meta_o[0], top_dst_y_o[0]};
  assign sample[((N_SRC+1)*(64+16+1)) +: (64+16+1)] = {top_dst_valid_o[1], top_dst_meta_o[1], top_dst_y_o[1]};
  assign sample[((N_SRC+N_TOP_DST+0)*(64+16+1)) +: (64+16+1)] = {cluster_valid_o[0], cluster_meta_o[0], cluster_y_o[0]};
  assign sample[((N_SRC+N_TOP_DST+1)*(64+16+1)) +: (64+16+1)] = {cluster_valid_o[1], cluster_meta_o[1], cluster_y_o[1]};

  sg_chain_core #(
    .P_W(24), .P_ALT(0), .P_SEED0(64'h0123_4567_89ab_cdef), .P_CONST0(16'h11a7), .P_CONST1(16'h22b9)
  ) i_src0 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[0]), .hold_i(src_hold_i[0]),
    .data_i(src_data_i[0]), .cfg_i(src_cfg_i[0]), .seed_i(src_seed_i[0]),
    .y_o(src_y_o[0]), .meta_o(src_meta_o[0]), .valid_o(src_valid_o[0])
  );
  sg_chain_core #(
    .P_W(24), .P_ALT(0), .P_SEED0(64'h0123_4567_89ab_cdef), .P_CONST0(16'h11a7), .P_CONST1(16'h22b9)
  ) i_src1 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[1]), .hold_i(src_hold_i[1]),
    .data_i(src_data_i[1]), .cfg_i(src_cfg_i[1]), .seed_i(src_seed_i[1]),
    .y_o(src_y_o[1]), .meta_o(src_meta_o[1]), .valid_o(src_valid_o[1])
  );
  sg_chain_core #(
    .P_W(40), .P_ALT(1), .P_SEED0(64'ha5a5_7788_99aa_bbcc), .P_CONST0(16'h39c1), .P_CONST1(16'h0d27)
  ) i_src2 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[2]), .hold_i(src_hold_i[2]),
    .data_i(src_data_i[2]), .cfg_i(src_cfg_i[2]), .seed_i(src_seed_i[2]),
    .y_o(src_y_o[2]), .meta_o(src_meta_o[2]), .valid_o(src_valid_o[2])
  );
  sg_chain_core #(
    .P_W(40), .P_ALT(1), .P_SEED0(64'ha5a5_7788_99aa_bbcc), .P_CONST0(16'h39c1), .P_CONST1(16'h0d27)
  ) i_src3 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[3]), .hold_i(src_hold_i[3]),
    .data_i(src_data_i[3]), .cfg_i(src_cfg_i[3]), .seed_i(src_seed_i[3]),
    .y_o(src_y_o[3]), .meta_o(src_meta_o[3]), .valid_o(src_valid_o[3])
  );
  sg_chain_core #(
    .P_W(56), .P_ALT(0), .P_SEED0(64'h55aa_963c_5bd1_e995), .P_CONST0(16'h5d3e), .P_CONST1(16'h71f0)
  ) i_src4 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[4]), .hold_i(src_hold_i[4]),
    .data_i(src_data_i[4]), .cfg_i(src_cfg_i[4]), .seed_i(src_seed_i[4]),
    .y_o(src_y_o[4]), .meta_o(src_meta_o[4]), .valid_o(src_valid_o[4])
  );
  sg_chain_core #(
    .P_W(32), .P_ALT(1), .P_SEED0(64'hdead_beef_cafe_f00d), .P_CONST0(16'h4e91), .P_CONST1(16'ha37c)
  ) i_src5 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[5]), .hold_i(src_hold_i[5]),
    .data_i(src_data_i[5]), .cfg_i(src_cfg_i[5]), .seed_i(src_seed_i[5]),
    .y_o(src_y_o[5]), .meta_o(src_meta_o[5]), .valid_o(src_valid_o[5])
  );

  sg_chain_core #(
    .P_W(24), .P_ALT(0), .P_SEED0(64'h0123_4567_89ab_cdef), .P_CONST0(16'h11a7), .P_CONST1(16'h22b9)
  ) i_dst0 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_dst_valid_i[0]), .hold_i(top_dst_hold_i[0]),
    .data_i(top_dst_data_i[0]), .cfg_i(top_dst_cfg_i[0]), .seed_i(top_dst_seed_i[0]),
    .y_o(top_dst_y_o[0]), .meta_o(top_dst_meta_o[0]), .valid_o(top_dst_valid_o[0])
  );
  sg_chain_core #(
    .P_W(40), .P_ALT(1), .P_SEED0(64'ha5a5_7788_99aa_bbcc), .P_CONST0(16'h39c1), .P_CONST1(16'h0d27)
  ) i_dst1 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_dst_valid_i[1]), .hold_i(top_dst_hold_i[1]),
    .data_i(top_dst_data_i[1]), .cfg_i(top_dst_cfg_i[1]), .seed_i(top_dst_seed_i[1]),
    .y_o(top_dst_y_o[1]), .meta_o(top_dst_meta_o[1]), .valid_o(top_dst_valid_o[1])
  );

  sg_chain_cluster i_cluster (
    .clk(clk),
    .rst_n(rst_n),
    .valid_i(cluster_in_valid_i),
    .hold_i(cluster_in_hold_i),
    .data_i(cluster_in_data_i),
    .cfg_i(cluster_in_cfg_i),
    .seed_i(cluster_in_seed_i),
    .y_o(cluster_y_o),
    .meta_o(cluster_meta_o),
    .valid_o(cluster_valid_o)
  );

  initial begin
    cyc = 0;
    rst_n = 1'b0;
    stim_a = 64'h243f_6a88_85a3_08d3;
    stim_b = 64'h1319_8a2e_0370_7344;
    stim_c = 32'ha409_3822;
    crc = 32'hffff_ffff;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    rst_n <= (cyc >= 3) && !((cyc >= 68) && (cyc < 71));
    stim_a <= lfsr64(stim_a) ^ {stim_b[31:0], stim_b[63:32]} ^ {32'(cyc * 7), 32'(cyc * 13)};
    stim_b <= lfsr64(stim_b ^ 64'hc001_cafe_5eed_f00d) + {stim_a[15:0], stim_a[63:16]};
    stim_c <= {stim_c[30:0], stim_c[31] ^ stim_c[21] ^ stim_c[1] ^ stim_c[0]} ^ 32'(cyc * 29);

    if ((cyc > 11) && !((cyc >= 68) && (cyc < 74))) crc <= crc32_bits(crc, sample);

    if (cyc == 220) begin
      $write("crc=%08x\n", crc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_chain_cluster (
  input  logic              clk,
  input  logic              rst_n,
  input  logic [1:0]        valid_i,
  input  logic [1:0]        hold_i,
  input  logic [1:0][63:0]  data_i,
  input  logic [1:0][15:0]  cfg_i,
  input  logic [1:0][7:0]   seed_i,
  output logic [1:0][63:0]  y_o,
  output logic [1:0][15:0]  meta_o,
  output logic [1:0]        valid_o
);

  sg_chain_core #(
    .P_W(56), .P_ALT(0), .P_SEED0(64'h55aa_963c_5bd1_e995), .P_CONST0(16'h5d3e), .P_CONST1(16'h71f0)
  ) i_cluster0 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[0]), .hold_i(hold_i[0]), .data_i(data_i[0]),
    .cfg_i(cfg_i[0]), .seed_i(seed_i[0]), .y_o(y_o[0]), .meta_o(meta_o[0]), .valid_o(valid_o[0])
  );

  sg_chain_core #(
    .P_W(48), .P_ALT(1), .P_SEED0(64'h0f1e_2d3c_4b5a_6978), .P_CONST0(16'h26d3), .P_CONST1(16'h18e5)
  ) i_cluster1 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[1]), .hold_i(hold_i[1]), .data_i(data_i[1]),
    .cfg_i(cfg_i[1]), .seed_i(seed_i[1]), .y_o(y_o[1]), .meta_o(meta_o[1]), .valid_o(valid_o[1])
  );

endmodule

module sg_chain_core #(
  parameter int unsigned P_W = 32,
  parameter bit          P_ALT = 0,
  parameter logic [63:0] P_SEED0 = 64'h0123_4567_89ab_cdef,
  parameter logic [15:0] P_CONST0 = 16'h1d3b,
  parameter logic [15:0] P_CONST1 = 16'h2a79
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic        hold_i,
  input  logic [63:0] data_i,
  input  logic [15:0] cfg_i,
  input  logic [7:0]  seed_i,
  output logic [63:0] y_o,
  output logic [15:0] meta_o,
  output logic        valid_o
); /*verilator subgraph_boundary*/

  sg_chain_pipe #(
    .P_W(P_W),
    .P_ALT(P_ALT),
    .P_SEED0(P_SEED0),
    .P_CONST0(P_CONST0),
    .P_CONST1(P_CONST1)
  ) i_pipe (
    .clk(clk),
    .rst_n(rst_n),
    .valid_i(valid_i),
    .hold_i(hold_i),
    .data_i(data_i),
    .cfg_i(cfg_i),
    .seed_i(seed_i),
    .y_o(y_o),
    .meta_o(meta_o),
    .valid_o(valid_o)
  );

endmodule

module sg_chain_pipe #(
  parameter int unsigned P_W = 32,
  parameter bit          P_ALT = 0,
  parameter logic [63:0] P_SEED0 = 64'h0123_4567_89ab_cdef,
  parameter logic [15:0] P_CONST0 = 16'h1d3b,
  parameter logic [15:0] P_CONST1 = 16'h2a79
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic        hold_i,
  input  logic [63:0] data_i,
  input  logic [15:0] cfg_i,
  input  logic [7:0]  seed_i,
  output logic [63:0] y_o,
  output logic [15:0] meta_o,
  output logic        valid_o
);

  logic [P_W-1:0] state_q;
  logic [P_W-1:0] acc_q;
  logic [P_W-1:0] lane_q;
  logic [P_W-1:0] data_q;
  logic [P_W-1:0] cfg_q;
  logic [7:0] seed_q;
  logic hold_q;
  logic [2:0] valid_q;

  logic [P_W-1:0] fold_w;
  logic [P_W-1:0] mix0_w;
  logic [P_W-1:0] mix1_w;

  function automatic logic [P_W-1:0] narrow64(input logic [63:0] x);
    logic [P_W-1:0] lo;
    logic [P_W-1:0] hi;
    lo = x[P_W-1:0];
    hi = (P_W'(x >> (64 - P_W)));
    return lo ^ hi ^ P_W'({P_CONST0, P_CONST1, P_CONST0, P_CONST1});
  endfunction

  function automatic logic [P_W-1:0] rotl(input logic [P_W-1:0] x, input int sh);
    int amt;
    amt = sh % P_W;
    if (amt == 0) return x;
    return (x << amt) | (x >> (P_W - amt));
  endfunction

  function automatic logic [63:0] widen64(input logic [P_W-1:0] x);
    logic [63:0] t;
    t = 64'(x) ^ (64'(x) << (P_W % 17)) ^ (64'(x) << ((P_W / 2) % 23));
    return t ^ {P_CONST0, P_CONST1, P_CONST0, P_CONST1};
  endfunction

  generate
    if (P_ALT) begin : gen_alt
      sg_chain_fold_alt #(.P_W(P_W), .P_CONST(P_CONST0)) i_fold (
        .a_i(state_q),
        .b_i(acc_q),
        .cfg_i(cfg_q),
        .y_o(fold_w)
      );
    end else begin : gen_base
      sg_chain_fold_base #(.P_W(P_W), .P_CONST(P_CONST1)) i_fold (
        .a_i(state_q),
        .b_i(acc_q),
        .cfg_i(cfg_q),
        .y_o(fold_w)
      );
    end
  endgenerate

  always_comb begin
    mix0_w = rotl(data_q ^ state_q ^ cfg_q ^ P_W'(seed_q), (P_W / 3) + 5);
    mix1_w = rotl(fold_w + lane_q + P_W'(seed_q ^ cfg_q[7:0]), (P_W / 5) + 9);
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state_q <= narrow64(P_SEED0);
      acc_q <= narrow64({P_SEED0[31:0], P_SEED0[63:32]});
      lane_q <= narrow64(P_SEED0 ^ 64'hc001_cafe_dead_beef);
      data_q <= '0;
      cfg_q <= '0;
      seed_q <= '0;
      hold_q <= 1'b0;
      valid_q <= '0;
      y_o <= '0;
      meta_o <= '0;
      valid_o <= 1'b0;
    end else begin
      data_q <= narrow64(data_i);
      cfg_q <= P_W'(cfg_i) ^ P_W'(seed_i);
      seed_q <= seed_i;
      hold_q <= hold_i;
      valid_q <= {valid_q[1:0], valid_i};

      if (valid_q[0] && !hold_q) begin
        state_q <= rotl(mix0_w ^ fold_w ^ lane_q, (P_W / 7) + 3);
        acc_q <= rotl(acc_q + mix1_w + P_W'(P_CONST0), (P_W / 9) + 1);
        lane_q <= rotl((lane_q ^ mix0_w) + P_W'(P_CONST1), (P_W / 11) + 5);
      end else if (hold_q) begin
        state_q <= state_q ^ P_W'(cfg_q ^ P_W'(P_CONST1));
        acc_q <= acc_q + P_W'(seed_q) + P_W'(P_CONST0);
        lane_q <= lane_q ^ rotl(acc_q, (P_W / 13) + 3);
      end else begin
        state_q <= rotl(state_q + P_W'(P_CONST0), (P_W / 5) + 7);
        acc_q <= acc_q ^ mix1_w ^ P_W'(P_CONST1);
        lane_q <= lane_q + rotl(state_q ^ acc_q, (P_W / 3) + 1);
      end

      y_o <= widen64(state_q) ^ (widen64(acc_q) >> 1) ^ (widen64(lane_q) << 1);
      meta_o <= cfg_q[15:0] ^ state_q[15:0] ^ acc_q[15:0] ^ {8'h0, seed_q};
      valid_o <= valid_q[2];
    end
  end

endmodule

module sg_chain_fold_base #(
  parameter int unsigned P_W = 32,
  parameter logic [15:0] P_CONST = 16'h1d3b
) (
  input  logic [P_W-1:0] a_i,
  input  logic [P_W-1:0] b_i,
  input  logic [P_W-1:0] cfg_i,
  output logic [P_W-1:0] y_o
);

  always_comb begin
    y_o = {a_i[P_W-2:0], a_i[P_W-1]}
          ^ {b_i[0], b_i[P_W-1:1]}
          ^ cfg_i
          ^ P_W'({P_CONST, P_CONST, P_CONST, P_CONST});
  end

endmodule

module sg_chain_fold_alt #(
  parameter int unsigned P_W = 32,
  parameter logic [15:0] P_CONST = 16'h2a79
) (
  input  logic [P_W-1:0] a_i,
  input  logic [P_W-1:0] b_i,
  input  logic [P_W-1:0] cfg_i,
  output logic [P_W-1:0] y_o
);

  always_comb begin
    y_o = (a_i + cfg_i)
          ^ ({b_i[P_W-9:0], b_i[P_W-1:P_W-8]})
          ^ P_W'({P_CONST, ~P_CONST, P_CONST, ~P_CONST});
  end

endmodule
