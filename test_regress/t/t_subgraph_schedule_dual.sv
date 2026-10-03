// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

package sg_dual_pkg;
  typedef struct packed {
    logic [15:0] x;
    logic [15:0] y;
    logic [15:0] z;
  } triple_t;

  typedef struct packed {
    logic signed [15:0] a;
    logic [15:0]        b;
    logic signed [15:0] c;
  } triple_signed_t;
endpackage

module t (
  input logic clk
);
  import sg_dual_pkg::*;

  localparam int N_TOP = 6;
  localparam int N_CLUSTER = 4;
  localparam int N_TOTAL = N_TOP + N_CLUSTER;
  localparam int SAMPLE_BITS = N_TOTAL * (64 + 16 + 1 + 2 + 64 + 16 + 1 + 2);

  int cyc;
  logic rst_n;
  logic [63:0] stim_a;
  logic [63:0] stim_b;
  logic [31:0] stim_c;
  logic [31:0] crc;

  logic [N_TOP-1:0]             top_valid_i;
  logic [N_TOP-1:0]             top_hold_i;
  logic [N_TOP-1:0][63:0]       top_a_i;
  logic [N_TOP-1:0][63:0]       top_b_i;
  logic [N_TOP-1:0][15:0]       top_cfg_i;
  logic [N_TOP-1:0][7:0]        top_mask_i;
  logic [N_TOP-1:0][63:0]       top_y0_o;
  logic [N_TOP-1:0][15:0]       top_m0_o;
  logic [N_TOP-1:0][1:0]        top_s0_o;
  logic [N_TOP-1:0]             top_v0_o;
  logic [N_TOP-1:0][63:0]       top_y1_o;
  logic [N_TOP-1:0][15:0]       top_m1_o;
  logic [N_TOP-1:0][1:0]        top_s1_o;
  logic [N_TOP-1:0]             top_v1_o;

  logic [N_CLUSTER-1:0][63:0]   cl_y0_o;
  logic [N_CLUSTER-1:0][15:0]   cl_m0_o;
  logic [N_CLUSTER-1:0][1:0]    cl_s0_o;
  logic [N_CLUSTER-1:0]         cl_v0_o;
  logic [N_CLUSTER-1:0][63:0]   cl_y1_o;
  logic [N_CLUSTER-1:0][15:0]   cl_m1_o;
  logic [N_CLUSTER-1:0][1:0]    cl_s1_o;
  logic [N_CLUSTER-1:0]         cl_v1_o;

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
    for (genvar g = 0; g < N_TOP; g++) begin : gen_top
      localparam logic [63:0] K64 = 64'h9e37_79b9_7f4a_7c15 ^ (64'h0102_0408_1020_4081 * (g + 1));
      localparam logic [15:0] K16 = 16'h4d31 ^ (16'h1273 * (g + 3));
      assign top_valid_i[g] = rst_n && (((cyc + g) % 5) != 2) && (((cyc ^ (g * 5)) & 4) == 0);
      assign top_hold_i[g] = (((cyc + (g * 3)) & 7) == 5);
      assign top_a_i[g] = stim_a ^ {stim_c, ~stim_c} ^ K64 ^ (64'(cyc + 5) << (g % 9));
      assign top_b_i[g] = stim_b + {32'(cyc * (g + 7)), stim_c} + {48'b0, K16};
      assign top_cfg_i[g] = stim_b[15:0] ^ K16 ^ 16'(cyc * (g + 9));
      assign top_mask_i[g] = stim_a[7:0] ^ stim_b[23:16] ^ 8'(g * 8'h21) ^ 8'(cyc);
      assign sample[(g*(64+16+1+2+64+16+1+2)) +: (64+16+1+2+64+16+1+2)] =
        {top_v1_o[g], top_s1_o[g], top_m1_o[g], top_y1_o[g], top_v0_o[g], top_s0_o[g], top_m0_o[g], top_y0_o[g]};
    end
  endgenerate

  sg_dual_node #(
    .P_STATE_T(triple_t), .P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h17)
  ) i_top0 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[0]), .hold_i(top_hold_i[0]),
    .a_i(top_a_i[0]), .b_i(top_b_i[0]), .cfg_i(top_cfg_i[0]), .mask_i(top_mask_i[0]),
    .y0_o(top_y0_o[0]), .meta0_o(top_m0_o[0]), .state0_o(top_s0_o[0]), .valid0_o(top_v0_o[0]),
    .y1_o(top_y1_o[0]), .meta1_o(top_m1_o[0]), .state1_o(top_s1_o[0]), .valid1_o(top_v1_o[0])
  );
  sg_dual_node #(
    .P_STATE_T(triple_t), .P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h17)
  ) i_top1 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[1]), .hold_i(top_hold_i[1]),
    .a_i(top_a_i[1]), .b_i(top_b_i[1]), .cfg_i(top_cfg_i[1]), .mask_i(top_mask_i[1]),
    .y0_o(top_y0_o[1]), .meta0_o(top_m0_o[1]), .state0_o(top_s0_o[1]), .valid0_o(top_v0_o[1]),
    .y1_o(top_y1_o[1]), .meta1_o(top_m1_o[1]), .state1_o(top_s1_o[1]), .valid1_o(top_v1_o[1])
  );
  sg_dual_node #(
    .P_STATE_T(triple_signed_t), .P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h2b)
  ) i_top2 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[2]), .hold_i(top_hold_i[2]),
    .a_i(top_a_i[2]), .b_i(top_b_i[2]), .cfg_i(top_cfg_i[2]), .mask_i(top_mask_i[2]),
    .y0_o(top_y0_o[2]), .meta0_o(top_m0_o[2]), .state0_o(top_s0_o[2]), .valid0_o(top_v0_o[2]),
    .y1_o(top_y1_o[2]), .meta1_o(top_m1_o[2]), .state1_o(top_s1_o[2]), .valid1_o(top_v1_o[2])
  );
  sg_dual_node #(
    .P_STATE_T(triple_signed_t), .P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h2b)
  ) i_top3 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[3]), .hold_i(top_hold_i[3]),
    .a_i(top_a_i[3]), .b_i(top_b_i[3]), .cfg_i(top_cfg_i[3]), .mask_i(top_mask_i[3]),
    .y0_o(top_y0_o[3]), .meta0_o(top_m0_o[3]), .state0_o(top_s0_o[3]), .valid0_o(top_v0_o[3]),
    .y1_o(top_y1_o[3]), .meta1_o(top_m1_o[3]), .state1_o(top_s1_o[3]), .valid1_o(top_v1_o[3])
  );
  sg_dual_node #(
    .P_STATE_T(triple_t), .P_ALT(1), .P_TAG(16'h6b8d), .P_BIAS(8'h39)
  ) i_top4 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[4]), .hold_i(top_hold_i[4]),
    .a_i(top_a_i[4]), .b_i(top_b_i[4]), .cfg_i(top_cfg_i[4]), .mask_i(top_mask_i[4]),
    .y0_o(top_y0_o[4]), .meta0_o(top_m0_o[4]), .state0_o(top_s0_o[4]), .valid0_o(top_v0_o[4]),
    .y1_o(top_y1_o[4]), .meta1_o(top_m1_o[4]), .state1_o(top_s1_o[4]), .valid1_o(top_v1_o[4])
  );
  sg_dual_node #(
    .P_STATE_T(triple_signed_t), .P_ALT(0), .P_TAG(16'h7f43), .P_BIAS(8'h4f)
  ) i_top5 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[5]), .hold_i(top_hold_i[5]),
    .a_i(top_a_i[5]), .b_i(top_b_i[5]), .cfg_i(top_cfg_i[5]), .mask_i(top_mask_i[5]),
    .y0_o(top_y0_o[5]), .meta0_o(top_m0_o[5]), .state0_o(top_s0_o[5]), .valid0_o(top_v0_o[5]),
    .y1_o(top_y1_o[5]), .meta1_o(top_m1_o[5]), .state1_o(top_s1_o[5]), .valid1_o(top_v1_o[5])
  );

  sg_dual_cluster i_cluster (
    .clk(clk),
    .rst_n(rst_n),
    .cyc_i(cyc),
    .stim_a(stim_a),
    .stim_b(stim_b),
    .stim_c(stim_c),
    .src_y0_i(top_y0_o),
    .src_m0_i(top_m0_o),
    .src_s0_i(top_s0_o),
    .src_v0_i(top_v0_o),
    .src_y1_i(top_y1_o),
    .src_m1_i(top_m1_o),
    .src_s1_i(top_s1_o),
    .src_v1_i(top_v1_o),
    .y0_o(cl_y0_o),
    .m0_o(cl_m0_o),
    .s0_o(cl_s0_o),
    .v0_o(cl_v0_o),
    .y1_o(cl_y1_o),
    .m1_o(cl_m1_o),
    .s1_o(cl_s1_o),
    .v1_o(cl_v1_o)
  );

  generate
    for (genvar g = 0; g < N_CLUSTER; g++) begin : gen_cl_sample
      assign sample[((N_TOP+g)*(64+16+1+2+64+16+1+2)) +: (64+16+1+2+64+16+1+2)] =
        {cl_v1_o[g], cl_s1_o[g], cl_m1_o[g], cl_y1_o[g], cl_v0_o[g], cl_s0_o[g], cl_m0_o[g], cl_y0_o[g]};
    end
  endgenerate

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
    rst_n <= (cyc >= 3) && !((cyc >= 76) && (cyc < 79));
    stim_a <= lfsr64(stim_a) ^ {stim_b[31:0], stim_b[63:32]} ^ {32'(cyc * 7), 32'(cyc * 19)};
    stim_b <= lfsr64(stim_b ^ 64'hc001_cafe_5eed_f00d) + {stim_a[15:0], stim_a[63:16]};
    stim_c <= {stim_c[30:0], stim_c[31] ^ stim_c[21] ^ stim_c[1] ^ stim_c[0]} ^ 32'(cyc * 29);

    if ((cyc > 12) && !((cyc >= 76) && (cyc < 82))) crc <= crc32_bits(crc, sample);

    if (cyc == 240) begin
      $write("crc=%08x\n", crc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_dual_cluster (
  input  logic              clk,
  input  logic              rst_n,
  input  int                cyc_i,
  input  logic [63:0]       stim_a,
  input  logic [63:0]       stim_b,
  input  logic [31:0]       stim_c,
  input  logic [5:0][63:0]  src_y0_i,
  input  logic [5:0][15:0]  src_m0_i,
  input  logic [5:0][1:0]   src_s0_i,
  input  logic [5:0]        src_v0_i,
  input  logic [5:0][63:0]  src_y1_i,
  input  logic [5:0][15:0]  src_m1_i,
  input  logic [5:0][1:0]   src_s1_i,
  input  logic [5:0]        src_v1_i,
  output logic [3:0][63:0]  y0_o,
  output logic [3:0][15:0]  m0_o,
  output logic [3:0][1:0]   s0_o,
  output logic [3:0]        v0_o,
  output logic [3:0][63:0]  y1_o,
  output logic [3:0][15:0]  m1_o,
  output logic [3:0][1:0]   s1_o,
  output logic [3:0]        v1_o
);
  import sg_dual_pkg::*;

  logic [3:0]        valid_i;
  logic [3:0]        hold_i;
  logic [3:0][63:0]  a_i;
  logic [3:0][63:0]  b_i;
  logic [3:0][15:0]  cfg_i;
  logic [3:0][7:0]   mask_i;

  generate
    for (genvar g = 0; g < 4; g++) begin : gen_in
      localparam int A = g;
      localparam int B = g + 2;
      assign valid_i[g] = rst_n && src_v0_i[A] && src_v1_i[B] && (((cyc_i + g) % 6) != 3);
      assign hold_i[g] = (((cyc_i + g + 4) & 7) == 2);
      assign a_i[g] = src_y0_i[A] ^ {src_m1_i[B], src_y1_i[B][47:0]} ^ stim_a;
      assign b_i[g] = src_y1_i[A] + {src_m0_i[B], src_y0_i[B][47:0]} + stim_b;
      assign cfg_i[g] = src_m0_i[A] ^ src_m1_i[B] ^ {12'b0, src_s0_i[A], src_s1_i[B]};
      assign mask_i[g] = src_y0_i[A][7:0] ^ src_y1_i[B][15:8] ^ 8'(cyc_i + (g * 11));
    end
  endgenerate

  sg_dual_node #(
    .P_STATE_T(triple_t), .P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h17)
  ) i_c0 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[0]), .hold_i(hold_i[0]), .a_i(a_i[0]), .b_i(b_i[0]),
    .cfg_i(cfg_i[0]), .mask_i(mask_i[0]), .y0_o(y0_o[0]), .meta0_o(m0_o[0]), .state0_o(s0_o[0]), .valid0_o(v0_o[0]),
    .y1_o(y1_o[0]), .meta1_o(m1_o[0]), .state1_o(s1_o[0]), .valid1_o(v1_o[0])
  );
  sg_dual_node #(
    .P_STATE_T(triple_signed_t), .P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h2b)
  ) i_c1 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[1]), .hold_i(hold_i[1]), .a_i(a_i[1]), .b_i(b_i[1]),
    .cfg_i(cfg_i[1]), .mask_i(mask_i[1]), .y0_o(y0_o[1]), .meta0_o(m0_o[1]), .state0_o(s0_o[1]), .valid0_o(v0_o[1]),
    .y1_o(y1_o[1]), .meta1_o(m1_o[1]), .state1_o(s1_o[1]), .valid1_o(v1_o[1])
  );
  sg_dual_node #(
    .P_STATE_T(triple_t), .P_ALT(1), .P_TAG(16'h6b8d), .P_BIAS(8'h39)
  ) i_c2 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[2]), .hold_i(hold_i[2]), .a_i(a_i[2]), .b_i(b_i[2]),
    .cfg_i(cfg_i[2]), .mask_i(mask_i[2]), .y0_o(y0_o[2]), .meta0_o(m0_o[2]), .state0_o(s0_o[2]), .valid0_o(v0_o[2]),
    .y1_o(y1_o[2]), .meta1_o(m1_o[2]), .state1_o(s1_o[2]), .valid1_o(v1_o[2])
  );
  sg_dual_node #(
    .P_STATE_T(triple_signed_t), .P_ALT(0), .P_TAG(16'h7f43), .P_BIAS(8'h4f)
  ) i_c3 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[3]), .hold_i(hold_i[3]), .a_i(a_i[3]), .b_i(b_i[3]),
    .cfg_i(cfg_i[3]), .mask_i(mask_i[3]), .y0_o(y0_o[3]), .meta0_o(m0_o[3]), .state0_o(s0_o[3]), .valid0_o(v0_o[3]),
    .y1_o(y1_o[3]), .meta1_o(m1_o[3]), .state1_o(s1_o[3]), .valid1_o(v1_o[3])
  );

endmodule

module sg_dual_node #(
  parameter type          P_STATE_T = sg_dual_pkg::triple_t,
  parameter bit           P_ALT = 0,
  parameter logic [15:0]  P_TAG = 16'h3141,
  parameter logic [7:0]   P_BIAS = 8'h17
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic        hold_i,
  input  logic [63:0] a_i,
  input  logic [63:0] b_i,
  input  logic [15:0] cfg_i,
  input  logic [7:0]  mask_i,
  output logic [63:0] y0_o,
  output logic [15:0] meta0_o,
  output logic [1:0]  state0_o,
  output logic        valid0_o,
  output logic [63:0] y1_o,
  output logic [15:0] meta1_o,
  output logic [1:0]  state1_o,
  output logic        valid1_o
); /*verilator subgraph_boundary*/
  localparam int SW = $bits(P_STATE_T);

  P_STATE_T state0_q [0:1];
  P_STATE_T state1_q [0:1];
  logic [SW-1:0] st0_bits [0:1];
  logic [SW-1:0] st1_bits [0:1];
  logic [63:0]   fold0_mix;
  logic [63:0]   fold1_mix;
  logic [63:0]   aux0_mix;
  logic [63:0]   aux1_mix;
  logic [31:0]   acc0_q;
  logic [31:0]   acc1_q;
  logic [63:0]   y0_q;
  logic [63:0]   y1_q;
  logic [15:0]   m0_q;
  logic [15:0]   m1_q;
  logic [1:0]    s0_q;
  logic [1:0]    s1_q;
  logic          v0_q;
  logic          v1_q;

  function automatic logic [63:0] zext64(input logic [SW-1:0] v);
    logic [63:0] tmp;
    tmp = 64'b0;
    tmp[SW-1:0] = v;
    return tmp;
  endfunction

  function automatic logic [SW-1:0] clipw(input logic [63:0] v);
    logic [SW-1:0] tmp;
    tmp = v[SW-1:0];
    return tmp;
  endfunction

  always_comb begin
    st0_bits[0] = SW'(state0_q[0]);
    st0_bits[1] = SW'(state0_q[1]);
    st1_bits[0] = SW'(state1_q[0]);
    st1_bits[1] = SW'(state1_q[1]);

    fold0_mix = zext64(st0_bits[0]) ^ {zext64(st0_bits[1])[31:0], a_i[31:0]};
    aux0_mix = zext64(st0_bits[1]) + {32'b0, acc0_q} + {48'b0, cfg_i};
    fold1_mix = zext64(st1_bits[0]) ^ {zext64(st1_bits[1])[31:0], b_i[31:0]};
    aux1_mix = zext64(st1_bits[1]) + {32'b0, acc1_q} + {56'b0, mask_i};

    if (P_ALT) begin
      fold0_mix ^= {b_i[23:0], b_i[63:24]};
      aux0_mix ^= {a_i[15:0], a_i[63:16]};
      fold1_mix += {a_i[23:0], a_i[63:24]};
      aux1_mix ^= {b_i[15:0], b_i[63:16]};
    end else begin
      fold0_mix += {a_i[15:0], a_i[63:16]};
      aux0_mix ^= {b_i[23:0], b_i[63:24]};
      fold1_mix ^= {b_i[15:0], b_i[63:16]};
      aux1_mix += {a_i[23:0], a_i[63:24]};
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      state0_q[0] <= P_STATE_T'({P_TAG, P_TAG ^ 16'h1111, P_TAG ^ 16'h2222});
      state0_q[1] <= P_STATE_T'({P_TAG ^ 16'h3333, P_TAG ^ 16'h4444, P_TAG ^ 16'h5555});
      state1_q[0] <= P_STATE_T'({P_TAG ^ 16'h6666, P_TAG ^ 16'h7777, P_TAG ^ 16'h8888});
      state1_q[1] <= P_STATE_T'({P_TAG ^ 16'h9999, P_TAG ^ 16'haaaa, P_TAG ^ 16'hbbbb});
      acc0_q <= {16'h510e, P_TAG};
      acc1_q <= {16'h1f83, P_TAG ^ 16'h0f0f};
      v0_q <= 1'b0;
      v1_q <= 1'b0;
    end else begin
      v0_q <= valid_i;
      v1_q <= valid_i ^ hold_i;
      if (valid_i) begin
        state0_q[0] <= P_STATE_T'(clipw(a_i ^ aux0_mix));
        if (!hold_i) state0_q[1] <= P_STATE_T'(clipw(fold0_mix ^ {32'b0, acc0_q}));
        state1_q[0] <= P_STATE_T'(clipw(b_i ^ aux1_mix));
        if (hold_i) state1_q[1] <= P_STATE_T'(clipw(fold1_mix + {32'b0, acc1_q}));
        acc0_q <= {acc0_q[15:0], acc0_q[31:16]} ^ a_i[31:0] ^ {16'b0, cfg_i};
        acc1_q <= {acc1_q[7:0], acc1_q[31:8]} ^ b_i[31:0] ^ {24'b0, mask_i};
      end else begin
        state0_q[0] <= P_STATE_T'(clipw(aux0_mix + {56'b0, P_BIAS}));
        state1_q[1] <= P_STATE_T'(clipw(aux1_mix ^ {56'b0, P_BIAS}));
        if (!hold_i) begin
          acc0_q <= acc0_q + {24'b0, P_BIAS} + {16'b0, cfg_i};
          acc1_q <= acc1_q + {24'b0, P_BIAS} + {24'b0, mask_i};
        end
      end
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      y0_q <= {32'h6a09_e667, 16'h0000, P_TAG};
      y1_q <= {32'hbb67_ae85, 16'h0000, P_TAG ^ 16'h1111};
      m0_q <= P_TAG ^ 16'h00f0;
      m1_q <= P_TAG ^ 16'h0f00;
      s0_q <= 2'b00;
      s1_q <= 2'b01;
    end else begin
      y0_q <= fold0_mix ^ aux0_mix ^ {acc0_q, cfg_i, mask_i, P_BIAS};
      y1_q <= fold1_mix ^ aux1_mix ^ {acc1_q, cfg_i, P_BIAS, mask_i};
      m0_q <= cfg_i ^ acc0_q[15:0] ^ {8'b0, mask_i};
      m1_q <= cfg_i ^ acc1_q[15:0] ^ {8'b0, mask_i ^ P_BIAS};
      s0_q <= {hold_i, valid_i};
      s1_q <= {P_ALT, hold_i ^ valid_i};
    end
  end

  assign y0_o = y0_q;
  assign meta0_o = m0_q;
  assign state0_o = s0_q;
  assign valid0_o = v0_q;
  assign y1_o = y1_q;
  assign meta1_o = m1_q;
  assign state1_o = s1_q;
  assign valid1_o = v1_q;

endmodule
