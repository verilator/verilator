// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

module t (
  input logic clk
);

  localparam int N_LEAF = 8;
  localparam int N_DOM = 2;
  localparam int LEAF_BITS = 64 + 16 + 1 + 3;
  localparam int AGG_BITS = 64 + 16 + 1 + 3;
  localparam int SAMPLE_BITS = (N_LEAF * LEAF_BITS) + (N_DOM * AGG_BITS) + AGG_BITS;

  int cyc;
  logic rst_n;
  logic [63:0] stim_a;
  logic [63:0] stim_b;
  logic [31:0] stim_c;
  logic [31:0] crc;

  logic [N_LEAF-1:0]        valid_i;
  logic [N_LEAF-1:0][63:0]  data_i;
  logic [N_LEAF-1:0][15:0]  cfg_i;
  logic [N_LEAF-1:0][7:0]   mask_i;

  logic [N_LEAF-1:0][63:0]  leaf_y_o;
  logic [N_LEAF-1:0][15:0]  leaf_tag_o;
  logic [N_LEAF-1:0][2:0]   leaf_state_o;
  logic [N_LEAF-1:0]        leaf_valid_o;

  logic [N_DOM-1:0][63:0]   dom_digest_o;
  logic [N_DOM-1:0][15:0]   dom_meta_o;
  logic [N_DOM-1:0][2:0]    dom_state_o;
  logic [N_DOM-1:0]         dom_valid_o;

  logic [63:0]              glob_digest_o;
  logic [15:0]              glob_meta_o;
  logic [2:0]               glob_state_o;
  logic                     glob_valid_o;

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
    for (genvar g = 0; g < N_LEAF; g++) begin : gen_in
      localparam logic [63:0] K64 = 64'h9e37_79b9_7f4a_7c15 ^ (64'h0102_0408_1020_4081 * (g + 1));
      localparam logic [15:0] K16 = 16'h53a7 ^ (16'h1073 * (g + 3));

      assign valid_i[g] = rst_n && (((cyc + g) % 5) != 2) && (((cyc ^ (g * 7)) & 4) == 0);
      assign data_i[g] = stim_a ^ {stim_c, ~stim_c} ^ K64 ^ (64'(cyc + 5) << (g % 9));
      assign cfg_i[g] = stim_b[15:0] ^ K16 ^ 16'(cyc * (g + 5));
      assign mask_i[g] = stim_a[7:0] ^ stim_b[23:16] ^ 8'(cyc + (g * 8'h1b));
      assign sample[(g*LEAF_BITS) +: LEAF_BITS] = {leaf_valid_o[g], leaf_state_o[g], leaf_tag_o[g], leaf_y_o[g]};
    end
  endgenerate

  assign sample[(N_LEAF*LEAF_BITS) +: AGG_BITS] = {dom_valid_o[0], dom_state_o[0], dom_meta_o[0], dom_digest_o[0]};
  assign sample[(N_LEAF*LEAF_BITS) + AGG_BITS +: AGG_BITS] = {dom_valid_o[1], dom_state_o[1], dom_meta_o[1], dom_digest_o[1]};
  assign sample[(N_LEAF*LEAF_BITS) + (N_DOM*AGG_BITS) +: AGG_BITS] = {glob_valid_o, glob_state_o, glob_meta_o, glob_digest_o};

  sg_fabric_system i_sys (
    .clk(clk),
    .rst_n(rst_n),
    .valid_i(valid_i),
    .data_i(data_i),
    .cfg_i(cfg_i),
    .mask_i(mask_i),
    .leaf_y_o(leaf_y_o),
    .leaf_tag_o(leaf_tag_o),
    .leaf_state_o(leaf_state_o),
    .leaf_valid_o(leaf_valid_o),
    .dom_digest_o(dom_digest_o),
    .dom_meta_o(dom_meta_o),
    .dom_state_o(dom_state_o),
    .dom_valid_o(dom_valid_o),
    .glob_digest_o(glob_digest_o),
    .glob_meta_o(glob_meta_o),
    .glob_state_o(glob_state_o),
    .glob_valid_o(glob_valid_o)
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
    rst_n <= (cyc >= 3) && !((cyc >= 88) && (cyc < 91));
    stim_a <= lfsr64(stim_a) ^ {stim_b[31:0], stim_b[63:32]} ^ {32'(cyc * 11), 32'(cyc * 19)};
    stim_b <= lfsr64(stim_b ^ 64'hc001_cafe_5eed_f00d) + {stim_a[23:0], stim_a[63:24]};
    stim_c <= {stim_c[30:0], stim_c[31] ^ stim_c[21] ^ stim_c[1] ^ stim_c[0]} ^ 32'(cyc * 29);

    if ((cyc > 12) && !((cyc >= 88) && (cyc < 94))) crc <= crc32_bits(crc, sample);

    if (cyc == 260) begin
      $write("crc=%08x\n", crc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_fabric_system (
  input  logic              clk,
  input  logic              rst_n,
  input  logic [7:0]        valid_i,
  input  logic [7:0][63:0]  data_i,
  input  logic [7:0][15:0]  cfg_i,
  input  logic [7:0][7:0]   mask_i,
  output logic [7:0][63:0]  leaf_y_o,
  output logic [7:0][15:0]  leaf_tag_o,
  output logic [7:0][2:0]   leaf_state_o,
  output logic [7:0]        leaf_valid_o,
  output logic [1:0][63:0]  dom_digest_o,
  output logic [1:0][15:0]  dom_meta_o,
  output logic [1:0][2:0]   dom_state_o,
  output logic [1:0]        dom_valid_o,
  output logic [63:0]       glob_digest_o,
  output logic [15:0]       glob_meta_o,
  output logic [2:0]        glob_state_o,
  output logic              glob_valid_o
);

  logic [3:0]        d0_valid_i;
  logic [3:0][63:0]  d0_data_i;
  logic [3:0][15:0]  d0_cfg_i;
  logic [3:0][7:0]   d0_mask_i;

  logic [3:0]        d1_valid_i;
  logic [3:0][63:0]  d1_data_i;
  logic [3:0][15:0]  d1_cfg_i;
  logic [3:0][7:0]   d1_mask_i;

  logic [3:0][63:0]  d0_leaf_y;
  logic [3:0][15:0]  d0_leaf_tag;
  logic [3:0][2:0]   d0_leaf_state;
  logic [3:0]        d0_leaf_valid;

  logic [3:0][63:0]  d1_leaf_y;
  logic [3:0][15:0]  d1_leaf_tag;
  logic [3:0][2:0]   d1_leaf_state;
  logic [3:0]        d1_leaf_valid;

  logic [1:0]        pick_valid;
  logic [1:0][1:0]   pick_idx;
  logic [1:0][63:0]  pick_digest;
  logic [1:0][15:0]  pick_tag;
  logic [1:0][2:0]   pick_state;

  logic              glob_pick_valid;
  logic              glob_pick_idx;
  logic [63:0]       glob_pick_digest;
  logic [15:0]       glob_pick_tag;
  logic [2:0]        glob_pick_state;

  logic [63:0] glob_digest_q;
  logic [15:0] glob_meta_q;
  logic [2:0]  glob_state_q;
  logic        glob_valid_q;
  logic [31:0] glob_acc_q;

  generate
    for (genvar g = 0; g < 4; g++) begin : gen_split
      assign d0_valid_i[g] = valid_i[g];
      assign d0_data_i[g] = data_i[g];
      assign d0_cfg_i[g] = cfg_i[g];
      assign d0_mask_i[g] = mask_i[g];

      assign d1_valid_i[g] = valid_i[g + 4];
      assign d1_data_i[g] = data_i[g + 4];
      assign d1_cfg_i[g] = cfg_i[g + 4];
      assign d1_mask_i[g] = mask_i[g + 4];

      assign leaf_y_o[g] = d0_leaf_y[g];
      assign leaf_tag_o[g] = d0_leaf_tag[g];
      assign leaf_state_o[g] = d0_leaf_state[g];
      assign leaf_valid_o[g] = d0_leaf_valid[g];

      assign leaf_y_o[g + 4] = d1_leaf_y[g];
      assign leaf_tag_o[g + 4] = d1_leaf_tag[g];
      assign leaf_state_o[g + 4] = d1_leaf_state[g];
      assign leaf_valid_o[g + 4] = d1_leaf_valid[g];
    end
  endgenerate

  sg_fabric_domain #(.P_DOMAIN_ID(0)) i_dom0 (
    .clk(clk),
    .rst_n(rst_n),
    .valid_i(d0_valid_i),
    .data_i(d0_data_i),
    .cfg_i(d0_cfg_i),
    .mask_i(d0_mask_i),
    .leaf_y_o(d0_leaf_y),
    .leaf_tag_o(d0_leaf_tag),
    .leaf_state_o(d0_leaf_state),
    .leaf_valid_o(d0_leaf_valid),
    .dom_digest_o(dom_digest_o[0]),
    .dom_meta_o(dom_meta_o[0]),
    .dom_state_o(dom_state_o[0]),
    .dom_valid_o(dom_valid_o[0]),
    .pick_valid_o(pick_valid[0]),
    .pick_idx_o(pick_idx[0]),
    .pick_digest_o(pick_digest[0]),
    .pick_tag_o(pick_tag[0]),
    .pick_state_o(pick_state[0])
  );

  sg_fabric_domain #(.P_DOMAIN_ID(1)) i_dom1 (
    .clk(clk),
    .rst_n(rst_n),
    .valid_i(d1_valid_i),
    .data_i(d1_data_i),
    .cfg_i(d1_cfg_i),
    .mask_i(d1_mask_i),
    .leaf_y_o(d1_leaf_y),
    .leaf_tag_o(d1_leaf_tag),
    .leaf_state_o(d1_leaf_state),
    .leaf_valid_o(d1_leaf_valid),
    .dom_digest_o(dom_digest_o[1]),
    .dom_meta_o(dom_meta_o[1]),
    .dom_state_o(dom_state_o[1]),
    .dom_valid_o(dom_valid_o[1]),
    .pick_valid_o(pick_valid[1]),
    .pick_idx_o(pick_idx[1]),
    .pick_digest_o(pick_digest[1]),
    .pick_tag_o(pick_tag[1]),
    .pick_state_o(pick_state[1])
  );

  sg_fabric_pick2 i_pick2 (
    .valid_i(dom_valid_o),
    .digest_i(dom_digest_o),
    .meta_i(dom_meta_o),
    .state_i(dom_state_o),
    .pick_valid_o(glob_pick_valid),
    .pick_idx_o(glob_pick_idx),
    .pick_digest_o(glob_pick_digest),
    .pick_meta_o(glob_pick_tag),
    .pick_state_o(glob_pick_state)
  );

  always @(posedge clk) begin
    if (!rst_n) begin
      glob_digest_q <= 64'h6a09_e667_f3bc_c908;
      glob_meta_q <= 16'h3141;
      glob_state_q <= 3'b000;
      glob_valid_q <= 1'b0;
      glob_acc_q <= 32'h510e_527f;
    end else begin
      glob_valid_q <= glob_pick_valid;
      if (glob_pick_valid) begin
        glob_digest_q <= glob_pick_digest
                         ^ dom_digest_o[0]
                         ^ {dom_digest_o[1][31:0], dom_digest_o[0][63:32]}
                         ^ {32'b0, glob_acc_q};
        glob_meta_q <= glob_pick_tag ^ dom_meta_o[0] ^ dom_meta_o[1] ^ glob_acc_q[15:0];
        glob_state_q <= glob_pick_state ^ dom_state_o[0] ^ dom_state_o[1];
        glob_acc_q <= {glob_acc_q[7:0], glob_acc_q[31:8]}
                      ^ dom_digest_o[0][31:0]
                      ^ dom_digest_o[1][31:0]
                      ^ {16'b0, dom_meta_o[glob_pick_idx]};
      end else begin
        glob_digest_q <= glob_digest_q ^ {32'b0, glob_acc_q} ^ dom_digest_o[0] ^ dom_digest_o[1];
        glob_meta_q <= glob_meta_q + dom_meta_o[0] + dom_meta_o[1];
        glob_state_q <= glob_state_q ^ {dom_valid_o[1], dom_valid_o[0], glob_pick_idx};
        glob_acc_q <= glob_acc_q + 32'h1f83_d9ab;
      end
    end
  end

  assign glob_digest_o = glob_digest_q;
  assign glob_meta_o = glob_meta_q;
  assign glob_state_o = glob_state_q;
  assign glob_valid_o = glob_valid_q;

endmodule

module sg_fabric_domain #(
  parameter int P_DOMAIN_ID = 0
) (
  input  logic              clk,
  input  logic              rst_n,
  input  logic [3:0]        valid_i,
  input  logic [3:0][63:0]  data_i,
  input  logic [3:0][15:0]  cfg_i,
  input  logic [3:0][7:0]   mask_i,
  output logic [3:0][63:0]  leaf_y_o,
  output logic [3:0][15:0]  leaf_tag_o,
  output logic [3:0][2:0]   leaf_state_o,
  output logic [3:0]        leaf_valid_o,
  output logic [63:0]       dom_digest_o,
  output logic [15:0]       dom_meta_o,
  output logic [2:0]        dom_state_o,
  output logic              dom_valid_o,
  output logic              pick_valid_o,
  output logic [1:0]        pick_idx_o,
  output logic [63:0]       pick_digest_o,
  output logic [15:0]       pick_tag_o,
  output logic [2:0]        pick_state_o
);

  logic [63:0] dom_digest_q;
  logic [15:0] dom_meta_q;
  logic [2:0]  dom_state_q;
  logic        dom_valid_q;
  logic [31:0] dom_acc_q;

  sg_fabric_leaf #(.P_SEED0(32'h243f_6a88), .P_SEED1(32'h85a3_08d3), .P_BIAS(8'h17), .P_ROT(5)) i_leaf0 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[0]), .data_i(data_i[0]), .cfg_i(cfg_i[0]), .mask_i(mask_i[0]),
    .y_o(leaf_y_o[0]), .tag_o(leaf_tag_o[0]), .state_o(leaf_state_o[0]), .valid_o(leaf_valid_o[0])
  );
  sg_fabric_leaf #(.P_SEED0(32'h243f_6a88), .P_SEED1(32'h85a3_08d3), .P_BIAS(8'h17), .P_ROT(5)) i_leaf1 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[1]), .data_i(data_i[1]), .cfg_i(cfg_i[1]), .mask_i(mask_i[1]),
    .y_o(leaf_y_o[1]), .tag_o(leaf_tag_o[1]), .state_o(leaf_state_o[1]), .valid_o(leaf_valid_o[1])
  );
  sg_fabric_leaf #(.P_SEED0(32'h1319_8a2e), .P_SEED1(32'h0370_7344), .P_BIAS(8'h2b), .P_ROT(11)) i_leaf2 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[2]), .data_i(data_i[2]), .cfg_i(cfg_i[2]), .mask_i(mask_i[2]),
    .y_o(leaf_y_o[2]), .tag_o(leaf_tag_o[2]), .state_o(leaf_state_o[2]), .valid_o(leaf_valid_o[2])
  );
  sg_fabric_leaf #(.P_SEED0(32'ha409_3822), .P_SEED1(32'h299f_31d0), .P_BIAS(8'h39), .P_ROT(17)) i_leaf3 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[3]), .data_i(data_i[3]), .cfg_i(cfg_i[3]), .mask_i(mask_i[3]),
    .y_o(leaf_y_o[3]), .tag_o(leaf_tag_o[3]), .state_o(leaf_state_o[3]), .valid_o(leaf_valid_o[3])
  );

  sg_fabric_pick4 i_pick4 (
    .valid_i(leaf_valid_o),
    .digest_i(leaf_y_o),
    .meta_i(leaf_tag_o),
    .state_i(leaf_state_o),
    .pick_valid_o(pick_valid_o),
    .pick_idx_o(pick_idx_o),
    .pick_digest_o(pick_digest_o),
    .pick_meta_o(pick_tag_o),
    .pick_state_o(pick_state_o)
  );

  always @(posedge clk) begin
    if (!rst_n) begin
      dom_digest_q <= 64'hbb67_ae85_84ca_a73b ^ 64'(P_DOMAIN_ID);
      dom_meta_q <= 16'h2200 ^ 16'(P_DOMAIN_ID);
      dom_state_q <= 3'b000;
      dom_valid_q <= 1'b0;
      dom_acc_q <= 32'h1f83_d9ab ^ 32'(P_DOMAIN_ID);
    end else begin
      dom_valid_q <= pick_valid_o;
      if (pick_valid_o) begin
        dom_digest_q <= pick_digest_o
                        ^ leaf_y_o[0]
                        ^ {leaf_y_o[1][31:0], leaf_y_o[2][63:32]}
                        ^ {32'b0, dom_acc_q};
        dom_meta_q <= pick_tag_o ^ leaf_tag_o[0] ^ leaf_tag_o[1] ^ leaf_tag_o[2] ^ leaf_tag_o[3];
        dom_state_q <= pick_state_o ^ leaf_state_o[0] ^ leaf_state_o[1] ^ leaf_state_o[2] ^ leaf_state_o[3];
        dom_acc_q <= {dom_acc_q[15:0], dom_acc_q[31:16]}
                     ^ pick_digest_o[31:0]
                     ^ {16'b0, pick_tag_o};
      end else begin
        dom_digest_q <= dom_digest_q ^ leaf_y_o[0] ^ leaf_y_o[1] ^ leaf_y_o[2] ^ leaf_y_o[3];
        dom_meta_q <= dom_meta_q + leaf_tag_o[0] + leaf_tag_o[1] + leaf_tag_o[2] + leaf_tag_o[3];
        dom_state_q <= dom_state_q ^ {leaf_valid_o[2], leaf_valid_o[1], leaf_valid_o[0]};
        dom_acc_q <= dom_acc_q + 32'h9e37_79b9;
      end
    end
  end

  assign dom_digest_o = dom_digest_q;
  assign dom_meta_o = dom_meta_q;
  assign dom_state_o = dom_state_q;
  assign dom_valid_o = dom_valid_q;

endmodule

module sg_fabric_pick4 (
  input  logic [3:0]        valid_i,
  input  logic [3:0][63:0]  digest_i,
  input  logic [3:0][15:0]  meta_i,
  input  logic [3:0][2:0]   state_i,
  output logic              pick_valid_o,
  output logic [1:0]        pick_idx_o,
  output logic [63:0]       pick_digest_o,
  output logic [15:0]       pick_meta_o,
  output logic [2:0]        pick_state_o
);
  logic [7:0] best_score;

  always_comb begin
    pick_valid_o = 1'b0;
    pick_idx_o = 2'b00;
    pick_digest_o = 64'b0;
    pick_meta_o = 16'b0;
    pick_state_o = 3'b000;
    best_score = 8'h00;
    for (int i = 0; i < 4; i++) begin
      logic [7:0] score;
      score = {valid_i[i], state_i[i], meta_i[i][2:0], digest_i[i][0]};
      if (valid_i[i] && (!pick_valid_o || (score >= best_score))) begin
        pick_valid_o = 1'b1;
        pick_idx_o = i[1:0];
        pick_digest_o = digest_i[i];
        pick_meta_o = meta_i[i];
        pick_state_o = state_i[i];
        best_score = score;
      end
    end
  end
endmodule

module sg_fabric_pick2 (
  input  logic [1:0]        valid_i,
  input  logic [1:0][63:0]  digest_i,
  input  logic [1:0][15:0]  meta_i,
  input  logic [1:0][2:0]   state_i,
  output logic              pick_valid_o,
  output logic              pick_idx_o,
  output logic [63:0]       pick_digest_o,
  output logic [15:0]       pick_meta_o,
  output logic [2:0]        pick_state_o
);
  always_comb begin
    pick_valid_o = valid_i[0] | valid_i[1];
    if (valid_i[1] && (!valid_i[0] || ({state_i[1], meta_i[1][2:0]} >= {state_i[0], meta_i[0][2:0]}))) begin
      pick_idx_o = 1'b1;
      pick_digest_o = digest_i[1];
      pick_meta_o = meta_i[1];
      pick_state_o = state_i[1];
    end else begin
      pick_idx_o = 1'b0;
      pick_digest_o = digest_i[0];
      pick_meta_o = meta_i[0];
      pick_state_o = state_i[0];
    end
  end
endmodule

module sg_fabric_leaf #(
  parameter logic [31:0] P_SEED0 = 32'h243f_6a88,
  parameter logic [31:0] P_SEED1 = 32'h85a3_08d3,
  parameter logic [7:0]  P_BIAS = 8'h17,
  parameter int unsigned P_ROT = 5
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic [63:0] data_i,
  input  logic [15:0] cfg_i,
  input  logic [7:0]  mask_i,
  output logic [63:0] y_o,
  output logic [15:0] tag_o,
  output logic [2:0]  state_o,
  output logic        valid_o
); /*verilator subgraph_boundary*/

  logic [63:0] mix_q;
  logic [63:0] lane_q;
  logic [31:0] acc_q;
  logic [15:0] tag_q;
  logic [2:0]  state_q;
  logic        valid_q;

  logic [63:0] fold_mix;
  logic [63:0] next_lane;

  always_comb begin
    fold_mix = {mix_q[63-P_ROT:0], mix_q[63:64-P_ROT]} ^ data_i ^ {48'b0, cfg_i};
    next_lane = lane_q ^ {32'b0, acc_q} ^ {56'b0, mask_i} ^ {56'b0, P_BIAS};
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      mix_q <= {P_SEED0, P_SEED1};
      lane_q <= {P_SEED1, P_SEED0};
      acc_q <= P_SEED0 ^ P_SEED1;
      tag_q <= P_SEED0[15:0] ^ P_SEED1[15:0];
      state_q <= 3'b000;
      valid_q <= 1'b0;
    end else begin
      valid_q <= valid_i;
      if (valid_i) begin
        mix_q <= fold_mix ^ next_lane;
        lane_q <= next_lane + {cfg_i, mask_i, 40'b0};
        acc_q <= {acc_q[15:0], acc_q[31:16]} ^ data_i[31:0] ^ {16'b0, cfg_i};
        tag_q <= cfg_i ^ acc_q[15:0] ^ {8'b0, mask_i};
        state_q <= {valid_i, mask_i[0], cfg_i[0]};
      end else begin
        mix_q <= mix_q ^ next_lane;
        lane_q <= lane_q + {32'b0, acc_q};
        acc_q <= acc_q + 32'h9e37_79b9;
        tag_q <= tag_q + 16'h0117;
        state_q <= state_q ^ 3'b101;
      end
    end
  end

  assign y_o = mix_q ^ lane_q;
  assign tag_o = tag_q;
  assign state_o = state_q;
  assign valid_o = valid_q;

endmodule
