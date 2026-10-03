// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

package sg_flow_pkg;
  typedef struct packed {
    logic [15:0] lo;
    logic [15:0] hi;
  } pair32_t;

  typedef struct packed {
    logic [15:0] a;
    logic [15:0] b;
    logic [15:0] c;
  } triple48_t;
endpackage

module t (
  input logic clk
);
  import sg_flow_pkg::*;

  localparam int TOP_NODES = 4;
  localparam int CLUSTER_NODES = 4;
  localparam int TOTAL_NODES = TOP_NODES + CLUSTER_NODES;
  localparam int SAMPLE_BITS = TOTAL_NODES * (64 + 16 + 2);

  int cyc;
  logic rst_n;
  logic [63:0] stim_a;
  logic [63:0] stim_b;
  logic [31:0] stim_c;
  logic [31:0] crc;

  logic src0_valid_i;
  logic src0_consume_i;
  logic src0_ready_o;
  logic src0_valid_o;
  logic [63:0] src0_data_i;
  logic [63:0] src0_data_o;
  logic [31:0] src0_side_i;
  logic [31:0] src0_side_o;
  logic [7:0]  src0_ctrl_i;
  logic [15:0] src0_meta_o;
  logic [63:0] src0_digest_o;

  logic dst0_consume_i;
  logic dst0_ready_o;
  logic dst0_valid_o;
  logic [63:0] dst0_data_o;
  logic [31:0] dst0_side_o;
  logic [15:0] dst0_meta_o;
  logic [63:0] dst0_digest_o;
  logic dst0_ready_seen;

  logic src1_valid_i;
  logic src1_consume_i;
  logic src1_ready_o;
  logic src1_valid_o;
  logic [63:0] src1_data_i;
  logic [63:0] src1_data_o;
  pair32_t src1_side_i;
  pair32_t src1_side_o;
  logic [7:0]  src1_ctrl_i;
  logic [15:0] src1_meta_o;
  logic [63:0] src1_digest_o;

  logic dst1_consume_i;
  logic dst1_ready_o;
  logic dst1_valid_o;
  logic [63:0] dst1_data_o;
  pair32_t dst1_side_o;
  logic [15:0] dst1_meta_o;
  logic [63:0] dst1_digest_o;
  logic dst1_ready_seen;

  logic [1:0] cluster_valid_i;
  logic [1:0] cluster_consume_i;
  logic [1:0] cluster_ready_o;
  logic [1:0] cluster_valid_o;
  logic [1:0][63:0] cluster_data_i;
  logic [1:0][63:0] cluster_data_o;
  logic [1:0][15:0] cluster_meta_o;
  logic [1:0][63:0] cluster_digest_o;

  logic [1:0] cluster_pair_valid_i;
  logic [1:0] cluster_pair_consume_i;
  logic [1:0] cluster_pair_ready_o;
  logic [1:0] cluster_pair_valid_o;
  logic [1:0][63:0] cluster_pair_data_i;
  logic [1:0][63:0] cluster_pair_data_o;
  logic [1:0][15:0] cluster_pair_meta_o;
  logic [1:0][63:0] cluster_pair_digest_o;

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

  assign src0_valid_i = rst_n && (((cyc + 1) % 5) != 2) && (((cyc ^ 6) & 4) == 0);
  assign src0_data_i = stim_a ^ {stim_c, ~stim_c} ^ 64'h1020_3040_5060_7080 ^ (64'(cyc) << 9);
  assign src0_side_i = stim_b[31:0] ^ 32'h1c93_d5a7 ^ 32'(cyc * 9);
  assign src0_ctrl_i = stim_a[7:0] ^ stim_b[23:16] ^ 8'(cyc);
  assign src0_consume_i = dst0_ready_seen ^ (((cyc + 2) & 7) == 1);
  assign dst0_consume_i = (((cyc + 3) & 7) != 4);

  assign src1_valid_i = rst_n && (((cyc + 3) % 6) != 1) && (((cyc ^ 9) & 2) == 0);
  assign src1_data_i = {stim_c, stim_c ^ 32'h5eed_f00d} ^ 64'h89ab_cdef_0123_4567 ^ (64'(cyc) << 5);
  assign src1_side_i.lo = stim_a[15:0] ^ 16'h33c5 ^ 16'(cyc * 3);
  assign src1_side_i.hi = stim_b[31:16] + 16'h0f71 + 16'(cyc * 5);
  assign src1_ctrl_i = stim_b[15:8] ^ stim_c[7:0] ^ 8'(cyc * 3);
  assign src1_consume_i = dst1_ready_seen ^ (((cyc + 5) & 7) == 6);
  assign dst1_consume_i = (((cyc + 1) & 7) != 3);

  assign sample[(0*(64+16+2)) +: (64+16+2)] = {src0_ready_o, src0_valid_o, src0_meta_o, src0_digest_o};
  assign sample[(1*(64+16+2)) +: (64+16+2)] = {dst0_ready_o, dst0_valid_o, dst0_meta_o, dst0_digest_o};
  assign sample[(2*(64+16+2)) +: (64+16+2)] = {src1_ready_o, src1_valid_o, src1_meta_o, src1_digest_o};
  assign sample[(3*(64+16+2)) +: (64+16+2)] = {dst1_ready_o, dst1_valid_o, dst1_meta_o, dst1_digest_o};
  assign sample[(4*(64+16+2)) +: (64+16+2)] = {cluster_ready_o[0], cluster_valid_o[0], cluster_meta_o[0], cluster_digest_o[0]};
  assign sample[(5*(64+16+2)) +: (64+16+2)] = {cluster_ready_o[1], cluster_valid_o[1], cluster_meta_o[1], cluster_digest_o[1]};
  assign sample[(6*(64+16+2)) +: (64+16+2)] = {cluster_pair_ready_o[0], cluster_pair_valid_o[0], cluster_pair_meta_o[0], cluster_pair_digest_o[0]};
  assign sample[(7*(64+16+2)) +: (64+16+2)] = {cluster_pair_ready_o[1], cluster_pair_valid_o[1], cluster_pair_meta_o[1], cluster_pair_digest_o[1]};

  sg_stream_node #(
    .P_SIDE_T(logic [31:0]), .P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h25)
  ) i_src0 (
    .clk(clk), .rst_n(rst_n), .valid_i(src0_valid_i), .consume_i(src0_consume_i),
    .data_i(src0_data_i), .side_i(src0_side_i), .ctrl_i(src0_ctrl_i),
    .ready_o(src0_ready_o), .valid_o(src0_valid_o), .data_o(src0_data_o), .side_o(src0_side_o),
    .meta_o(src0_meta_o), .digest_o(src0_digest_o)
  );

  sg_stream_node #(
    .P_SIDE_T(logic [31:0]), .P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h25)
  ) i_dst0 (
    .clk(clk), .rst_n(rst_n), .valid_i(src0_valid_o), .consume_i(dst0_consume_i),
    .data_i(src0_data_o ^ {48'b0, src0_meta_o}), .side_i(src0_side_o ^ 32'h6a09_e667), .ctrl_i(src0_meta_o[7:0]),
    .ready_o(dst0_ready_o), .valid_o(dst0_valid_o), .data_o(dst0_data_o), .side_o(dst0_side_o),
    .meta_o(dst0_meta_o), .digest_o(dst0_digest_o)
  );

  sg_stream_node #(
    .P_SIDE_T(pair32_t), .P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h25)
  ) i_src1 (
    .clk(clk), .rst_n(rst_n), .valid_i(src1_valid_i), .consume_i(src1_consume_i),
    .data_i(src1_data_i), .side_i(src1_side_i), .ctrl_i(src1_ctrl_i),
    .ready_o(src1_ready_o), .valid_o(src1_valid_o), .data_o(src1_data_o), .side_o(src1_side_o),
    .meta_o(src1_meta_o), .digest_o(src1_digest_o)
  );

  sg_stream_node #(
    .P_SIDE_T(pair32_t), .P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h25)
  ) i_dst1 (
    .clk(clk), .rst_n(rst_n), .valid_i(src1_valid_o), .consume_i(dst1_consume_i),
    .data_i(src1_data_o + {48'b0, src1_meta_o}), .side_i('{lo: src1_side_o.hi ^ 16'h55aa, hi: src1_side_o.lo + 16'h1021}),
    .ctrl_i(src1_meta_o[15:8]),
    .ready_o(dst1_ready_o), .valid_o(dst1_valid_o), .data_o(dst1_data_o), .side_o(dst1_side_o),
    .meta_o(dst1_meta_o), .digest_o(dst1_digest_o)
  );

  sg_flow_cluster i_cluster (
    .clk(clk),
    .rst_n(rst_n),
    .stim_a(stim_a),
    .stim_b(stim_b),
    .stim_c(stim_c),
    .cyc_i(cyc),
    .valid_o(cluster_valid_o),
    .ready_o(cluster_ready_o),
    .meta_o(cluster_meta_o),
    .digest_o(cluster_digest_o),
    .pair_valid_o(cluster_pair_valid_o),
    .pair_ready_o(cluster_pair_ready_o),
    .pair_meta_o(cluster_pair_meta_o),
    .pair_digest_o(cluster_pair_digest_o)
  );

  initial begin
    cyc = 0;
    rst_n = 1'b0;
    stim_a = 64'h243f_6a88_85a3_08d3;
    stim_b = 64'h1319_8a2e_0370_7344;
    stim_c = 32'ha409_3822;
    crc = 32'hffff_ffff;
    dst0_ready_seen = 1'b0;
    dst1_ready_seen = 1'b0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    rst_n <= (cyc >= 3) && !((cyc >= 72) && (cyc < 75));
    stim_a <= lfsr64(stim_a) ^ {stim_b[31:0], stim_b[63:32]} ^ {32'(cyc * 7), 32'(cyc * 13)};
    stim_b <= lfsr64(stim_b ^ 64'hc001_cafe_5eed_f00d) + {stim_a[23:0], stim_a[63:24]};
    stim_c <= {stim_c[30:0], stim_c[31] ^ stim_c[21] ^ stim_c[1] ^ stim_c[0]} ^ 32'(cyc * 19);
    dst0_ready_seen <= dst0_ready_o;
    dst1_ready_seen <= dst1_ready_o;

    if ((cyc > 12) && !((cyc >= 72) && (cyc < 78))) crc <= crc32_bits(crc, sample);

    if (cyc == 240) begin
      $write("crc=%08x\n", crc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_flow_cluster (
  input  logic              clk,
  input  logic              rst_n,
  input  logic [63:0]       stim_a,
  input  logic [63:0]       stim_b,
  input  logic [31:0]       stim_c,
  input  int                cyc_i,
  output logic [1:0]        valid_o,
  output logic [1:0]        ready_o,
  output logic [1:0][15:0]  meta_o,
  output logic [1:0][63:0]  digest_o,
  output logic [1:0]        pair_valid_o,
  output logic [1:0]        pair_ready_o,
  output logic [1:0][15:0]  pair_meta_o,
  output logic [1:0][63:0]  pair_digest_o
);
  import sg_flow_pkg::*;

  logic logic0_valid_i;
  logic logic0_consume_i;
  logic logic0_ready_o;
  logic logic0_valid_o;
  logic [63:0] logic0_data_i;
  logic [63:0] logic0_data_o;
  logic [47:0] logic0_side_i;
  logic [47:0] logic0_side_o;
  logic [7:0]  logic0_ctrl_i;
  logic [15:0] logic0_meta_o;
  logic [63:0] logic0_digest_o;

  logic logic1_consume_i;
  logic logic1_ready_o;
  logic logic1_valid_o;
  logic [63:0] logic1_data_o;
  logic [47:0] logic1_side_o;
  logic [15:0] logic1_meta_o;
  logic [63:0] logic1_digest_o;

  logic pair0_valid_i;
  logic pair0_consume_i;
  logic pair0_ready_o;
  logic pair0_valid_o;
  logic [63:0] pair0_data_i;
  logic [63:0] pair0_data_o;
  triple48_t pair0_side_i;
  triple48_t pair0_side_o;
  logic [7:0]  pair0_ctrl_i;
  logic [15:0] pair0_meta_o;
  logic [63:0] pair0_digest_o;

  logic pair1_consume_i;
  logic pair1_ready_o;
  logic pair1_valid_o;
  logic [63:0] pair1_data_o;
  triple48_t pair1_side_o;
  logic [15:0] pair1_meta_o;
  logic [63:0] pair1_digest_o;
  logic logic1_ready_seen;
  logic pair1_ready_seen;

  assign logic0_valid_i = rst_n && (((cyc_i + 2) % 7) != 3) && (((cyc_i ^ 11) & 4) == 0);
  assign logic0_data_i = stim_b ^ {stim_c, ~stim_c} ^ 64'h55aa_963c_5bd1_e995 ^ (64'(cyc_i) << 7);
  assign logic0_side_i = stim_a[47:0] ^ 48'h12_3456_789a_bc;
  assign logic0_ctrl_i = stim_c[15:8] ^ stim_a[39:32] ^ 8'(cyc_i);
  assign logic0_consume_i = logic1_ready_seen ^ (((cyc_i + 4) & 7) == 2);
  assign logic1_consume_i = (((cyc_i + 6) & 7) != 5);

  assign pair0_valid_i = rst_n && (((cyc_i + 4) % 5) != 1) && (((cyc_i ^ 13) & 1) == 0);
  assign pair0_data_i = {stim_c ^ 32'h7654_3210, stim_c + 32'h1021_3045} ^ 64'h0f1e_2d3c_4b5a_6978;
  assign pair0_side_i.a = stim_a[15:0] ^ 16'h7ac1;
  assign pair0_side_i.b = stim_b[31:16] + 16'h2457;
  assign pair0_side_i.c = stim_a[47:32] ^ stim_c[15:0] ^ 16'h9e37;
  assign pair0_ctrl_i = stim_b[55:48] ^ stim_c[23:16] ^ 8'(cyc_i * 5);
  assign pair0_consume_i = pair1_ready_seen ^ (((cyc_i + 1) & 7) == 7);
  assign pair1_consume_i = (((cyc_i + 3) & 7) != 0);

  sg_stream_node #(
    .P_SIDE_T(logic [47:0]), .P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h39)
  ) i_logic0 (
    .clk(clk), .rst_n(rst_n), .valid_i(logic0_valid_i), .consume_i(logic0_consume_i),
    .data_i(logic0_data_i), .side_i(logic0_side_i), .ctrl_i(logic0_ctrl_i),
    .ready_o(logic0_ready_o), .valid_o(logic0_valid_o), .data_o(logic0_data_o), .side_o(logic0_side_o),
    .meta_o(logic0_meta_o), .digest_o(logic0_digest_o)
  );

  sg_stream_node #(
    .P_SIDE_T(logic [47:0]), .P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h39)
  ) i_logic1 (
    .clk(clk), .rst_n(rst_n), .valid_i(logic0_valid_o), .consume_i(logic1_consume_i),
    .data_i(logic0_data_o ^ {48'b0, logic0_meta_o}), .side_i(logic0_side_o ^ 48'h0ace_55aa_1122),
    .ctrl_i(logic0_meta_o[7:0]),
    .ready_o(logic1_ready_o), .valid_o(logic1_valid_o), .data_o(logic1_data_o), .side_o(logic1_side_o),
    .meta_o(logic1_meta_o), .digest_o(logic1_digest_o)
  );

  sg_stream_node #(
    .P_SIDE_T(triple48_t), .P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h39)
  ) i_pair0 (
    .clk(clk), .rst_n(rst_n), .valid_i(pair0_valid_i), .consume_i(pair0_consume_i),
    .data_i(pair0_data_i), .side_i(pair0_side_i), .ctrl_i(pair0_ctrl_i),
    .ready_o(pair0_ready_o), .valid_o(pair0_valid_o), .data_o(pair0_data_o), .side_o(pair0_side_o),
    .meta_o(pair0_meta_o), .digest_o(pair0_digest_o)
  );

  sg_stream_node #(
    .P_SIDE_T(triple48_t), .P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h39)
  ) i_pair1 (
    .clk(clk), .rst_n(rst_n), .valid_i(pair0_valid_o), .consume_i(pair1_consume_i),
    .data_i(pair0_data_o + {48'b0, pair0_meta_o}),
    .side_i('{a: pair0_side_o.c ^ 16'h5a5a, b: pair0_side_o.a + 16'h0c21, c: pair0_side_o.b ^ pair0_meta_o}),
    .ctrl_i(pair0_meta_o[15:8]),
    .ready_o(pair1_ready_o), .valid_o(pair1_valid_o), .data_o(pair1_data_o), .side_o(pair1_side_o),
    .meta_o(pair1_meta_o), .digest_o(pair1_digest_o)
  );

  assign valid_o = '{logic0_valid_o, logic1_valid_o};
  assign ready_o = '{logic0_ready_o, logic1_ready_o};
  assign meta_o = '{logic0_meta_o, logic1_meta_o};
  assign digest_o = '{logic0_digest_o, logic1_digest_o};

  assign pair_valid_o = '{pair0_valid_o, pair1_valid_o};
  assign pair_ready_o = '{pair0_ready_o, pair1_ready_o};
  assign pair_meta_o = '{pair0_meta_o, pair1_meta_o};
  assign pair_digest_o = '{pair0_digest_o, pair1_digest_o};

  initial begin
    logic1_ready_seen = 1'b0;
    pair1_ready_seen = 1'b0;
  end

  always @(posedge clk) begin
    logic1_ready_seen <= logic1_ready_o;
    pair1_ready_seen <= pair1_ready_o;
  end

endmodule

module sg_stream_node #(
  parameter type          P_SIDE_T = logic [31:0],
  parameter bit           P_ALT = 0,
  parameter logic [15:0]  P_TAG = 16'h3141,
  parameter logic [7:0]   P_BIAS = 8'h25
) (
  input  logic    clk,
  input  logic    rst_n,
  input  logic    valid_i,
  input  logic    consume_i,
  input  logic [63:0] data_i,
  input  P_SIDE_T side_i,
  input  logic [7:0] ctrl_i,
  output logic    ready_o,
  output logic    valid_o,
  output logic [63:0] data_o,
  output P_SIDE_T side_o,
  output logic [15:0] meta_o,
  output logic [63:0] digest_o
); /*verilator subgraph_boundary*/
  localparam int SIDE_W = $bits(P_SIDE_T);

  logic [SIDE_W-1:0] side_i_bits;
  logic [SIDE_W-1:0] side_q;
  logic [63:0] data_q;
  logic [31:0] acc_q;
  logic [15:0] seq_q;
  logic [7:0]  ctrl_q;
  logic        ready_q;
  logic        valid_q;

  logic [63:0] fold_side;
  logic [63:0] fold_state;
  logic [63:0] mix_seed;
  logic [31:0] side_crc;
  logic [SIDE_W-1:0] side_crc_w;
  logic        accept_i;
  logic        release_o;
  logic [15:0] meta_q;
  logic [63:0] digest_q;

  function automatic logic [63:0] zext64(input logic [SIDE_W-1:0] v);
    logic [63:0] tmp;
    tmp = 64'b0;
    tmp[SIDE_W-1:0] = v;
    return tmp;
  endfunction

  function automatic logic [31:0] crc32_vec(input logic [31:0] c_i, input logic [63:0] d_i);
    logic [31:0] c;
    c = c_i;
    for (int i = 0; i < 64; i++) begin
      logic feedback;
      feedback = c[31] ^ d_i[i];
      c = {c[30:0], 1'b0};
      if (feedback) c ^= 32'h04c11db7;
    end
    return c;
  endfunction

  function automatic logic [SIDE_W-1:0] zext_side(input logic [31:0] v);
    logic [SIDE_W-1:0] tmp;
    tmp = '0;
    tmp[31:0] = v;
    return tmp;
  endfunction

  assign side_i_bits = SIDE_W'(side_i);
  assign accept_i = valid_i && ready_q;
  assign release_o = valid_q && consume_i;
  assign mix_seed = data_i ^ zext64(side_i_bits) ^ {56'b0, ctrl_i} ^ {48'b0, P_TAG};
  assign side_crc = crc32_vec(acc_q ^ {16'b0, P_TAG}, mix_seed ^ data_q);
  assign side_crc_w = zext_side(side_crc);

  generate
    if (P_ALT) begin : gen_alt
      sg_stream_fold_alt #(.P_W(SIDE_W), .P_BIAS(P_BIAS)) i_fold (
        .side_i(side_q),
        .data_i(data_q),
        .acc_i(acc_q),
        .fold_side_o(fold_side),
        .fold_state_o(fold_state)
      );
    end else begin : gen_base
      sg_stream_fold_base #(.P_W(SIDE_W), .P_BIAS(P_BIAS)) i_fold (
        .side_i(side_q),
        .data_i(data_q),
        .acc_i(acc_q),
        .fold_side_o(fold_side),
        .fold_state_o(fold_state)
      );
    end
  endgenerate

  always @(posedge clk) begin
    if (!rst_n) begin
      ready_q <= 1'b1;
      valid_q <= 1'b0;
      seq_q <= P_TAG ^ 16'h00f0;
      ctrl_q <= P_BIAS;
      meta_q <= P_TAG ^ 16'h00aa;
      digest_q <= {32'h1234_5678, 16'h0000, P_TAG};
    end else begin
      if (release_o) ready_q <= 1'b1;
      else if (accept_i) ready_q <= 1'b0;

      if (release_o) valid_q <= 1'b0;
      if (accept_i) valid_q <= 1'b1;

      if (accept_i) begin
        seq_q <= seq_q + {8'b0, ctrl_i} + {8'b0, P_BIAS};
        ctrl_q <= ctrl_i ^ P_BIAS;
        meta_q <= (seq_q + {8'b0, ctrl_i}) ^ side_crc[15:0] ^ {8'b0, P_BIAS};
        digest_q <= data_q ^ fold_side ^ {acc_q, seq_q, ctrl_q, P_BIAS};
      end else if (valid_q) begin
        seq_q <= seq_q ^ acc_q[15:0] ^ {8'b0, ctrl_q};
        ctrl_q <= ctrl_q + seq_q[7:0] + P_BIAS;
        meta_q <= (seq_q ^ acc_q[15:0]) + {8'b0, ctrl_q};
        digest_q <= data_q + fold_state ^ {acc_q, seq_q, ctrl_q, P_BIAS};
      end
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      side_q <= SIDE_W'(P_TAG);
      data_q <= {32'h6a09_e667, 16'h0000, P_TAG};
      acc_q <= {16'h510e, P_TAG};
    end else if (accept_i) begin
      side_q <= side_i_bits ^ side_crc_w;
      data_q <= mix_seed + fold_side + {32'b0, side_crc};
      acc_q <= side_crc ^ data_i[31:0] ^ {16'b0, seq_q};
    end else if (valid_q) begin
      side_q <= side_q ^ fold_state[SIDE_W-1:0] ^ {SIDE_W{ctrl_q[0]}};
      data_q <= data_q ^ fold_side ^ {acc_q, side_crc};
      acc_q <= {acc_q[15:0], acc_q[31:16]} + side_crc + {24'b0, ctrl_q};
    end
  end

  assign ready_o = ready_q;
  assign valid_o = valid_q;
  assign side_o = P_SIDE_T'(side_q);
  assign data_o = data_q;
  assign meta_o = meta_q;
  assign digest_o = digest_q;

endmodule

module sg_stream_fold_base #(
  parameter int P_W = 32,
  parameter logic [7:0] P_BIAS = 8'h25
) (
  input  logic [P_W-1:0] side_i,
  input  logic [63:0]    data_i,
  input  logic [31:0]    acc_i,
  output logic [63:0]    fold_side_o,
  output logic [63:0]    fold_state_o
);
  logic [63:0] side64;
  always_comb begin
    side64 = 64'b0;
    side64[P_W-1:0] = side_i;
    fold_side_o = side64 ^ {acc_i, acc_i};
    fold_state_o = {data_i[31:0] ^ acc_i, data_i[63:32] + {24'b0, P_BIAS}};
  end
endmodule

module sg_stream_fold_alt #(
  parameter int P_W = 48,
  parameter logic [7:0] P_BIAS = 8'h39
) (
  input  logic [P_W-1:0] side_i,
  input  logic [63:0]    data_i,
  input  logic [31:0]    acc_i,
  output logic [63:0]    fold_side_o,
  output logic [63:0]    fold_state_o
);
  logic [63:0] side64;
  always_comb begin
    side64 = 64'b0;
    side64[P_W-1:0] = side_i;
    fold_side_o = {side64[15:0], side64[63:16]} + {data_i[23:0], data_i[63:24]} + {32'b0, acc_i};
    fold_state_o = (side64 ^ {acc_i, acc_i}) + {56'b0, P_BIAS};
  end
endmodule
