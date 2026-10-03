// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

module t (
  input logic clk
);

  localparam int N_STAGE0 = 4;
  localparam int N_STAGE1 = 4;
  localparam int N_STAGE2 = 4;
  localparam int N_TOTAL = N_STAGE0 + N_STAGE1 + N_STAGE2;
  localparam int SAMPLE_BITS = N_TOTAL * (64 + 16 + 1 + 2);

  int cyc;
  logic rst_n;
  logic [63:0] stim_a;
  logic [63:0] stim_b;
  logic [31:0] stim_c;
  logic [31:0] crc;

  logic [N_STAGE0-1:0]        s0_valid_i;
  logic [N_STAGE0-1:0]        s0_hold_i;
  logic [N_STAGE0-1:0][63:0]  s0_data_i;
  logic [N_STAGE0-1:0][15:0]  s0_cfg_i;
  logic [N_STAGE0-1:0][7:0]   s0_mask_i;
  logic [N_STAGE0-1:0][63:0]  s0_y_o;
  logic [N_STAGE0-1:0][15:0]  s0_meta_o;
  logic [N_STAGE0-1:0][1:0]   s0_state_o;
  logic [N_STAGE0-1:0]        s0_valid_o;

  logic [N_STAGE1-1:0]        s1_valid_i;
  logic [N_STAGE1-1:0]        s1_hold_i;
  logic [N_STAGE1-1:0][63:0]  s1_data_i;
  logic [N_STAGE1-1:0][15:0]  s1_cfg_i;
  logic [N_STAGE1-1:0][7:0]   s1_mask_i;
  logic [N_STAGE1-1:0][63:0]  s1_y_o;
  logic [N_STAGE1-1:0][15:0]  s1_meta_o;
  logic [N_STAGE1-1:0][1:0]   s1_state_o;
  logic [N_STAGE1-1:0]        s1_valid_o;

  logic [N_STAGE2-1:0][63:0]  s2_y_o;
  logic [N_STAGE2-1:0][15:0]  s2_meta_o;
  logic [N_STAGE2-1:0][1:0]   s2_state_o;
  logic [N_STAGE2-1:0]        s2_valid_o;

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
    for (genvar g = 0; g < N_STAGE0; g++) begin : gen_stage0
      localparam logic [63:0] K64 = 64'h9e37_79b9_7f4a_7c15 ^ (64'h0102_0408_1020_4081 * (g + 1));
      localparam logic [15:0] K16 = 16'h51c3 ^ (16'h1379 * (g + 3));
      assign s0_valid_i[g] = rst_n && (((cyc + g) % 5) != 2) && (((cyc ^ (g * 7)) & 4) == 0);
      assign s0_hold_i[g] = (((cyc + (g * 3)) & 7) == 5);
      assign s0_data_i[g] = stim_a ^ {stim_c, ~stim_c} ^ K64 ^ (64'(cyc + 1) << (g + 2));
      assign s0_cfg_i[g] = stim_b[15:0] ^ K16 ^ 16'(cyc * (g + 5));
      assign s0_mask_i[g] = stim_a[7:0] ^ stim_b[23:16] ^ 8'(g * 8'h17) ^ 8'(cyc);
      assign sample[(g*(64+16+1+2)) +: (64+16+1+2)] = {s0_valid_o[g], s0_state_o[g], s0_meta_o[g], s0_y_o[g]};
    end
  endgenerate

  generate
    for (genvar g = 0; g < N_STAGE1; g++) begin : gen_stage1
      localparam int SRC_A = g;
      localparam int SRC_B = (g + 1) % N_STAGE0;
      assign s1_valid_i[g] = rst_n && s0_valid_o[SRC_A] && (((cyc + g) & 3) != 1);
      assign s1_hold_i[g] = (((cyc + g + 2) & 7) == 6);
      assign s1_data_i[g] = s0_y_o[SRC_A] ^ {s0_meta_o[SRC_B], s0_y_o[SRC_B][47:0]} ^ {stim_c, stim_b[31:0]};
      assign s1_cfg_i[g] = s0_meta_o[SRC_A] + s0_meta_o[SRC_B] + 16'(g * 16'h1123);
      assign s1_mask_i[g] = s0_y_o[SRC_A][7:0] ^ s0_y_o[SRC_B][15:8] ^ 8'(cyc + (g * 9));
      assign sample[((N_STAGE0+g)*(64+16+1+2)) +: (64+16+1+2)] = {s1_valid_o[g], s1_state_o[g], s1_meta_o[g], s1_y_o[g]};
    end
  endgenerate

  generate
    for (genvar g = 0; g < N_STAGE2; g++) begin : gen_sample2
      assign sample[((N_STAGE0+N_STAGE1+g)*(64+16+1+2)) +: (64+16+1+2)] = {s2_valid_o[g], s2_state_o[g], s2_meta_o[g], s2_y_o[g]};
    end
  endgenerate

  sg_mem_node #(
    .P_W(24), .P_ALT(0), .P_SEED(32'h243f_6a88), .P_BIAS(8'h19)
  ) i_s0_0 (
    .clk(clk), .rst_n(rst_n), .valid_i(s0_valid_i[0]), .hold_i(s0_hold_i[0]), .data_i(s0_data_i[0]),
    .cfg_i(s0_cfg_i[0]), .mask_i(s0_mask_i[0]), .y_o(s0_y_o[0]), .meta_o(s0_meta_o[0]),
    .state_o(s0_state_o[0]), .valid_o(s0_valid_o[0])
  );
  sg_mem_node #(
    .P_W(24), .P_ALT(0), .P_SEED(32'h243f_6a88), .P_BIAS(8'h19)
  ) i_s0_1 (
    .clk(clk), .rst_n(rst_n), .valid_i(s0_valid_i[1]), .hold_i(s0_hold_i[1]), .data_i(s0_data_i[1]),
    .cfg_i(s0_cfg_i[1]), .mask_i(s0_mask_i[1]), .y_o(s0_y_o[1]), .meta_o(s0_meta_o[1]),
    .state_o(s0_state_o[1]), .valid_o(s0_valid_o[1])
  );
  sg_mem_node #(
    .P_W(40), .P_ALT(1), .P_SEED(32'h1319_8a2e), .P_BIAS(8'h2d)
  ) i_s0_2 (
    .clk(clk), .rst_n(rst_n), .valid_i(s0_valid_i[2]), .hold_i(s0_hold_i[2]), .data_i(s0_data_i[2]),
    .cfg_i(s0_cfg_i[2]), .mask_i(s0_mask_i[2]), .y_o(s0_y_o[2]), .meta_o(s0_meta_o[2]),
    .state_o(s0_state_o[2]), .valid_o(s0_valid_o[2])
  );
  sg_mem_node #(
    .P_W(40), .P_ALT(1), .P_SEED(32'h1319_8a2e), .P_BIAS(8'h2d)
  ) i_s0_3 (
    .clk(clk), .rst_n(rst_n), .valid_i(s0_valid_i[3]), .hold_i(s0_hold_i[3]), .data_i(s0_data_i[3]),
    .cfg_i(s0_cfg_i[3]), .mask_i(s0_mask_i[3]), .y_o(s0_y_o[3]), .meta_o(s0_meta_o[3]),
    .state_o(s0_state_o[3]), .valid_o(s0_valid_o[3])
  );

  sg_mem_node #(
    .P_W(40), .P_ALT(1), .P_SEED(32'h1319_8a2e), .P_BIAS(8'h2d)
  ) i_s1_0 (
    .clk(clk), .rst_n(rst_n), .valid_i(s1_valid_i[0]), .hold_i(s1_hold_i[0]), .data_i(s1_data_i[0]),
    .cfg_i(s1_cfg_i[0]), .mask_i(s1_mask_i[0]), .y_o(s1_y_o[0]), .meta_o(s1_meta_o[0]),
    .state_o(s1_state_o[0]), .valid_o(s1_valid_o[0])
  );
  sg_mem_node #(
    .P_W(32), .P_ALT(0), .P_SEED(32'ha409_3822), .P_BIAS(8'h37)
  ) i_s1_1 (
    .clk(clk), .rst_n(rst_n), .valid_i(s1_valid_i[1]), .hold_i(s1_hold_i[1]), .data_i(s1_data_i[1]),
    .cfg_i(s1_cfg_i[1]), .mask_i(s1_mask_i[1]), .y_o(s1_y_o[1]), .meta_o(s1_meta_o[1]),
    .state_o(s1_state_o[1]), .valid_o(s1_valid_o[1])
  );
  sg_mem_node #(
    .P_W(32), .P_ALT(0), .P_SEED(32'ha409_3822), .P_BIAS(8'h37)
  ) i_s1_2 (
    .clk(clk), .rst_n(rst_n), .valid_i(s1_valid_i[2]), .hold_i(s1_hold_i[2]), .data_i(s1_data_i[2]),
    .cfg_i(s1_cfg_i[2]), .mask_i(s1_mask_i[2]), .y_o(s1_y_o[2]), .meta_o(s1_meta_o[2]),
    .state_o(s1_state_o[2]), .valid_o(s1_valid_o[2])
  );
  sg_mem_node #(
    .P_W(56), .P_ALT(1), .P_SEED(32'h5bd1_e995), .P_BIAS(8'h41)
  ) i_s1_3 (
    .clk(clk), .rst_n(rst_n), .valid_i(s1_valid_i[3]), .hold_i(s1_hold_i[3]), .data_i(s1_data_i[3]),
    .cfg_i(s1_cfg_i[3]), .mask_i(s1_mask_i[3]), .y_o(s1_y_o[3]), .meta_o(s1_meta_o[3]),
    .state_o(s1_state_o[3]), .valid_o(s1_valid_o[3])
  );

  sg_mem_cluster i_cluster (
    .clk(clk),
    .rst_n(rst_n),
    .cyc_i(cyc),
    .stim_a(stim_a),
    .stim_b(stim_b),
    .stim_c(stim_c),
    .src_y_i(s1_y_o),
    .src_meta_i(s1_meta_o),
    .src_state_i(s1_state_o),
    .src_valid_i(s1_valid_o),
    .y_o(s2_y_o),
    .meta_o(s2_meta_o),
    .state_o(s2_state_o),
    .valid_o(s2_valid_o)
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
    rst_n <= (cyc >= 3) && !((cyc >= 74) && (cyc < 77));
    stim_a <= lfsr64(stim_a) ^ {stim_b[31:0], stim_b[63:32]} ^ {32'(cyc * 7), 32'(cyc * 11)};
    stim_b <= lfsr64(stim_b ^ 64'hc001_cafe_5eed_f00d) + {stim_a[15:0], stim_a[63:16]};
    stim_c <= {stim_c[30:0], stim_c[31] ^ stim_c[21] ^ stim_c[1] ^ stim_c[0]} ^ 32'(cyc * 23);

    if ((cyc > 12) && !((cyc >= 74) && (cyc < 80))) crc <= crc32_bits(crc, sample);

    if (cyc == 240) begin
      $write("crc=%08x\n", crc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_mem_cluster (
  input  logic              clk,
  input  logic              rst_n,
  input  int                cyc_i,
  input  logic [63:0]       stim_a,
  input  logic [63:0]       stim_b,
  input  logic [31:0]       stim_c,
  input  logic [3:0][63:0]  src_y_i,
  input  logic [3:0][15:0]  src_meta_i,
  input  logic [3:0][1:0]   src_state_i,
  input  logic [3:0]        src_valid_i,
  output logic [3:0][63:0]  y_o,
  output logic [3:0][15:0]  meta_o,
  output logic [3:0][1:0]   state_o,
  output logic [3:0]        valid_o
);

  logic [3:0]        valid_i;
  logic [3:0]        hold_i;
  logic [3:0][63:0]  data_i;
  logic [3:0][15:0]  cfg_i;
  logic [3:0][7:0]   mask_i;

  generate
    for (genvar g = 0; g < 4; g++) begin : gen_cluster_in
      localparam int SRC_A = g;
      localparam int SRC_B = (g + 2) % 4;
      assign valid_i[g] = rst_n && src_valid_i[SRC_A] && (((cyc_i + g) % 6) != 4);
      assign hold_i[g] = (((cyc_i + g + 1) & 7) == 3);
      assign data_i[g] = src_y_i[SRC_A] + {src_meta_i[SRC_B], src_y_i[SRC_B][47:0]} + stim_b;
      assign cfg_i[g] = src_meta_i[SRC_A] ^ {14'b0, src_state_i[SRC_B]} ^ stim_c[15:0] ^ 16'(g * 16'h045d);
      assign mask_i[g] = src_y_i[SRC_A][15:8] ^ src_y_i[SRC_B][7:0] ^ 8'(cyc_i + (g * 13));
    end
  endgenerate

  sg_mem_node #(
    .P_W(24), .P_ALT(0), .P_SEED(32'h243f_6a88), .P_BIAS(8'h19)
  ) i_n0 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[0]), .hold_i(hold_i[0]), .data_i(data_i[0]),
    .cfg_i(cfg_i[0]), .mask_i(mask_i[0]), .y_o(y_o[0]), .meta_o(meta_o[0]), .state_o(state_o[0]), .valid_o(valid_o[0])
  );
  sg_mem_node #(
    .P_W(24), .P_ALT(0), .P_SEED(32'h243f_6a88), .P_BIAS(8'h19)
  ) i_n1 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[1]), .hold_i(hold_i[1]), .data_i(data_i[1]),
    .cfg_i(cfg_i[1]), .mask_i(mask_i[1]), .y_o(y_o[1]), .meta_o(meta_o[1]), .state_o(state_o[1]), .valid_o(valid_o[1])
  );
  sg_mem_node #(
    .P_W(56), .P_ALT(1), .P_SEED(32'h5bd1_e995), .P_BIAS(8'h41)
  ) i_n2 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[2]), .hold_i(hold_i[2]), .data_i(data_i[2]),
    .cfg_i(cfg_i[2]), .mask_i(mask_i[2]), .y_o(y_o[2]), .meta_o(meta_o[2]), .state_o(state_o[2]), .valid_o(valid_o[2])
  );
  sg_mem_node #(
    .P_W(48), .P_ALT(1), .P_SEED(32'h0f1e_2d3c), .P_BIAS(8'h4b)
  ) i_n3 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[3]), .hold_i(hold_i[3]), .data_i(data_i[3]),
    .cfg_i(cfg_i[3]), .mask_i(mask_i[3]), .y_o(y_o[3]), .meta_o(meta_o[3]), .state_o(state_o[3]), .valid_o(valid_o[3])
  );

endmodule

module sg_mem_node #(
  parameter int unsigned P_W = 32,
  parameter bit          P_ALT = 0,
  parameter logic [31:0] P_SEED = 32'h243f_6a88,
  parameter logic [7:0]  P_BIAS = 8'h19
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic        hold_i,
  input  logic [63:0] data_i,
  input  logic [15:0] cfg_i,
  input  logic [7:0]  mask_i,
  output logic [63:0] y_o,
  output logic [15:0] meta_o,
  output logic [1:0]  state_o,
  output logic        valid_o
); /*verilator subgraph_boundary*/

  logic [P_W-1:0] mem_q [0:3];
  logic [P_W-1:0] write_mix;
  logic [P_W-1:0] read_mix;
  logic [63:0]    fold_mix;
  logic [63:0]    shadow_mix;
  logic [31:0]    acc_q;
  logic [63:0]    y_q;
  logic [15:0]    meta_q;
  logic [1:0]     state_q;
  logic [1:0]     wr_ptr_q;
  logic [1:0]     rd_ptr_q;
  logic [1:0]     phase_q;
  logic           valid_q;

  function automatic logic [63:0] zext64(input logic [P_W-1:0] v);
    logic [63:0] tmp;
    tmp = 64'b0;
    tmp[P_W-1:0] = v;
    return tmp;
  endfunction

  function automatic logic [P_W-1:0] clipw(input logic [63:0] v);
    logic [P_W-1:0] tmp;
    tmp = v[P_W-1:0];
    return tmp;
  endfunction

  always_comb begin
    read_mix = mem_q[rd_ptr_q] ^ mem_q[rd_ptr_q ^ 2'b01] ^ clipw({48'b0, cfg_i});
    if (P_ALT) read_mix ^= clipw({32'b0, data_i[31:0]});
    else read_mix ^= clipw({56'b0, mask_i});
  end

  always_comb begin
    write_mix = mem_q[wr_ptr_q] ^ mem_q[wr_ptr_q ^ 2'b10] ^ clipw(data_i);
    write_mix ^= clipw({32'b0, acc_q});
    write_mix ^= clipw({48'b0, cfg_i ^ {8'b0, mask_i}});
    if (P_ALT) write_mix = {write_mix[P_W-2:0], write_mix[P_W-1]} ^ clipw({56'b0, P_BIAS});
  end

  always_comb begin
    fold_mix = zext64(mem_q[0]) ^ {zext64(mem_q[1])[31:0], zext64(mem_q[2])[31:0]};
    shadow_mix = zext64(mem_q[3]) + {32'b0, acc_q} + {48'b0, cfg_i};
    if (P_ALT) begin
      fold_mix ^= {data_i[23:0], data_i[63:24]};
      shadow_mix ^= {data_i[31:0], 16'b0, cfg_i};
    end else begin
      fold_mix += {data_i[15:0], data_i[63:16]};
      shadow_mix ^= {56'b0, mask_i};
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      wr_ptr_q <= 2'b00;
      rd_ptr_q <= 2'b01;
      phase_q <= 2'b00;
      valid_q <= 1'b0;
    end else begin
      if (valid_i) begin
        wr_ptr_q <= wr_ptr_q + 2'b01;
        rd_ptr_q <= rd_ptr_q + 2'b11;
      end
      if (!hold_i) phase_q <= phase_q + 2'b01;
      valid_q <= valid_i;
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      mem_q[0] <= P_W'(P_SEED);
      mem_q[1] <= P_W'(P_SEED ^ 32'h9e37_79b9);
      mem_q[2] <= P_W'(P_SEED ^ 32'h3c6e_f372);
      mem_q[3] <= P_W'(P_SEED ^ 32'ha54f_f53a);
      acc_q <= P_SEED ^ {24'b0, P_BIAS};
    end else if (valid_i) begin
      mem_q[wr_ptr_q] <= write_mix;
      mem_q[wr_ptr_q ^ 2'b01] <= mem_q[wr_ptr_q ^ 2'b01] ^ read_mix;
      if (!hold_i) mem_q[rd_ptr_q] <= mem_q[rd_ptr_q] + clipw(shadow_mix);
      acc_q <= {acc_q[15:0], acc_q[31:16]} ^ data_i[31:0] ^ {16'b0, cfg_i} ^ {24'b0, mask_i};
    end else if (!hold_i) begin
      mem_q[phase_q] <= mem_q[phase_q] ^ clipw(fold_mix);
      acc_q <= acc_q + {24'b0, P_BIAS} + {16'b0, cfg_i};
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      y_q <= {32'h6a09_e667, P_SEED};
      meta_q <= P_SEED[15:0] ^ {8'b0, P_BIAS};
      state_q <= 2'b00;
    end else begin
      y_q <= fold_mix ^ shadow_mix ^ {acc_q, mem_q[phase_q][15:0], cfg_i};
      meta_q <= cfg_i ^ acc_q[15:0] ^ {8'b0, mask_i};
      state_q <= phase_q ^ {hold_i, valid_i};
    end
  end

  assign y_o = y_q;
  assign meta_o = meta_q;
  assign state_o = state_q;
  assign valid_o = valid_q;

endmodule
