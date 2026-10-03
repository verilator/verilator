// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

module t (
  input logic clk
);

  localparam int N_SRC = 4;
  localparam int N_MID = 4;
  localparam int N_DST = 4;
  localparam int N_TOTAL = N_SRC + N_MID + N_DST;
  localparam int SAMPLE_BITS = N_TOTAL * (64 + 16 + 1 + 3);

  int cyc;
  logic rst_n;
  logic [63:0] stim_a;
  logic [63:0] stim_b;
  logic [31:0] stim_c;
  logic [31:0] crc;

  logic [N_SRC-1:0]        src_valid_i;
  logic [N_SRC-1:0]        src_hold_i;
  logic [N_SRC-1:0]        src_flush_i;
  logic [N_SRC-1:0][63:0]  src_data_i;
  logic [N_SRC-1:0][15:0]  src_cfg_i;
  logic [N_SRC-1:0][7:0]   src_mask_i;
  logic [N_SRC-1:0][63:0]  src_y_o;
  logic [N_SRC-1:0][15:0]  src_meta_o;
  logic [N_SRC-1:0][2:0]   src_state_o;
  logic [N_SRC-1:0]        src_valid_o;

  logic [N_MID-1:0]        mid_valid_i;
  logic [N_MID-1:0]        mid_hold_i;
  logic [N_MID-1:0]        mid_flush_i;
  logic [N_MID-1:0][63:0]  mid_data_i;
  logic [N_MID-1:0][15:0]  mid_cfg_i;
  logic [N_MID-1:0][7:0]   mid_mask_i;
  logic [N_MID-1:0][63:0]  mid_y_o;
  logic [N_MID-1:0][15:0]  mid_meta_o;
  logic [N_MID-1:0][2:0]   mid_state_o;
  logic [N_MID-1:0]        mid_valid_o;

  logic [N_DST-1:0][63:0]  dst_y_o;
  logic [N_DST-1:0][15:0]  dst_meta_o;
  logic [N_DST-1:0][2:0]   dst_state_o;
  logic [N_DST-1:0]        dst_valid_o;

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
    for (genvar g = 0; g < N_SRC; g++) begin : gen_src
      localparam logic [63:0] K64 = 64'h9e37_79b9_7f4a_7c15 ^ (64'h0102_0408_1020_4081 * (g + 1));
      localparam logic [15:0] K16 = 16'h43b1 ^ (16'h1297 * (g + 5));
      assign src_valid_i[g] = rst_n && (((cyc + g) % 5) != 2) && (((cyc ^ (g * 11)) & 4) == 0);
      assign src_hold_i[g] = (((cyc + (g * 2)) & 7) == 4);
      assign src_flush_i[g] = rst_n && (((cyc + g) % 17) == 9);
      assign src_data_i[g] = stim_a ^ {stim_c, ~stim_c} ^ K64 ^ (64'(cyc + 3) << (g + 1));
      assign src_cfg_i[g] = stim_b[15:0] ^ K16 ^ 16'(cyc * (g + 7));
      assign src_mask_i[g] = stim_a[7:0] ^ stim_b[23:16] ^ 8'(g * 8'h19) ^ 8'(cyc);
      assign sample[(g*(64+16+1+3)) +: (64+16+1+3)] = {src_valid_o[g], src_state_o[g], src_meta_o[g], src_y_o[g]};
    end
  endgenerate

  generate
    for (genvar g = 0; g < N_MID; g++) begin : gen_mid
      localparam int A = g;
      localparam int B = (g + 1) % N_SRC;
      localparam int C = (g + 2) % N_SRC;
      assign mid_valid_i[g] = rst_n && src_valid_o[A] && src_valid_o[B] && (((cyc + g) & 3) != 1);
      assign mid_hold_i[g] = (((cyc + g + 3) & 7) == 6);
      assign mid_flush_i[g] = rst_n && (((cyc + g) % 19) == 7);
      assign mid_data_i[g] = src_y_o[A] ^ {src_meta_o[B], src_y_o[B][47:0]} ^ {src_y_o[C][31:0], stim_c};
      assign mid_cfg_i[g] = src_meta_o[A] + src_meta_o[B] + {13'b0, src_state_o[C]};
      assign mid_mask_i[g] = src_y_o[A][7:0] ^ src_y_o[B][15:8] ^ src_y_o[C][23:16] ^ 8'(cyc + (g * 7));
      assign sample[((N_SRC+g)*(64+16+1+3)) +: (64+16+1+3)] = {mid_valid_o[g], mid_state_o[g], mid_meta_o[g], mid_y_o[g]};
    end
  endgenerate

  generate
    for (genvar g = 0; g < N_DST; g++) begin : gen_sample_dst
      assign sample[((N_SRC+N_MID+g)*(64+16+1+3)) +: (64+16+1+3)] = {dst_valid_o[g], dst_state_o[g], dst_meta_o[g], dst_y_o[g]};
    end
  endgenerate

  sg_bank_node #(.P_W(24), .P_BANKS(1), .P_ALT(0), .P_SEED(32'h243f_6a88), .P_BIAS(8'h1b)) i_src0 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[0]), .hold_i(src_hold_i[0]), .flush_i(src_flush_i[0]),
    .data_i(src_data_i[0]), .cfg_i(src_cfg_i[0]), .mask_i(src_mask_i[0]),
    .y_o(src_y_o[0]), .meta_o(src_meta_o[0]), .state_o(src_state_o[0]), .valid_o(src_valid_o[0])
  );
  sg_bank_node #(.P_W(24), .P_BANKS(1), .P_ALT(0), .P_SEED(32'h243f_6a88), .P_BIAS(8'h1b)) i_src1 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[1]), .hold_i(src_hold_i[1]), .flush_i(src_flush_i[1]),
    .data_i(src_data_i[1]), .cfg_i(src_cfg_i[1]), .mask_i(src_mask_i[1]),
    .y_o(src_y_o[1]), .meta_o(src_meta_o[1]), .state_o(src_state_o[1]), .valid_o(src_valid_o[1])
  );
  sg_bank_node #(.P_W(40), .P_BANKS(2), .P_ALT(1), .P_SEED(32'h1319_8a2e), .P_BIAS(8'h2f)) i_src2 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[2]), .hold_i(src_hold_i[2]), .flush_i(src_flush_i[2]),
    .data_i(src_data_i[2]), .cfg_i(src_cfg_i[2]), .mask_i(src_mask_i[2]),
    .y_o(src_y_o[2]), .meta_o(src_meta_o[2]), .state_o(src_state_o[2]), .valid_o(src_valid_o[2])
  );
  sg_bank_node #(.P_W(40), .P_BANKS(2), .P_ALT(1), .P_SEED(32'h1319_8a2e), .P_BIAS(8'h2f)) i_src3 (
    .clk(clk), .rst_n(rst_n), .valid_i(src_valid_i[3]), .hold_i(src_hold_i[3]), .flush_i(src_flush_i[3]),
    .data_i(src_data_i[3]), .cfg_i(src_cfg_i[3]), .mask_i(src_mask_i[3]),
    .y_o(src_y_o[3]), .meta_o(src_meta_o[3]), .state_o(src_state_o[3]), .valid_o(src_valid_o[3])
  );

  sg_bank_node #(.P_W(32), .P_BANKS(1), .P_ALT(1), .P_SEED(32'ha409_3822), .P_BIAS(8'h35)) i_mid0 (
    .clk(clk), .rst_n(rst_n), .valid_i(mid_valid_i[0]), .hold_i(mid_hold_i[0]), .flush_i(mid_flush_i[0]),
    .data_i(mid_data_i[0]), .cfg_i(mid_cfg_i[0]), .mask_i(mid_mask_i[0]),
    .y_o(mid_y_o[0]), .meta_o(mid_meta_o[0]), .state_o(mid_state_o[0]), .valid_o(mid_valid_o[0])
  );
  sg_bank_node #(.P_W(32), .P_BANKS(1), .P_ALT(1), .P_SEED(32'ha409_3822), .P_BIAS(8'h35)) i_mid1 (
    .clk(clk), .rst_n(rst_n), .valid_i(mid_valid_i[1]), .hold_i(mid_hold_i[1]), .flush_i(mid_flush_i[1]),
    .data_i(mid_data_i[1]), .cfg_i(mid_cfg_i[1]), .mask_i(mid_mask_i[1]),
    .y_o(mid_y_o[1]), .meta_o(mid_meta_o[1]), .state_o(mid_state_o[1]), .valid_o(mid_valid_o[1])
  );
  sg_bank_node #(.P_W(56), .P_BANKS(2), .P_ALT(0), .P_SEED(32'h5bd1_e995), .P_BIAS(8'h47)) i_mid2 (
    .clk(clk), .rst_n(rst_n), .valid_i(mid_valid_i[2]), .hold_i(mid_hold_i[2]), .flush_i(mid_flush_i[2]),
    .data_i(mid_data_i[2]), .cfg_i(mid_cfg_i[2]), .mask_i(mid_mask_i[2]),
    .y_o(mid_y_o[2]), .meta_o(mid_meta_o[2]), .state_o(mid_state_o[2]), .valid_o(mid_valid_o[2])
  );
  sg_bank_node #(.P_W(48), .P_BANKS(2), .P_ALT(1), .P_SEED(32'h0f1e_2d3c), .P_BIAS(8'h53)) i_mid3 (
    .clk(clk), .rst_n(rst_n), .valid_i(mid_valid_i[3]), .hold_i(mid_hold_i[3]), .flush_i(mid_flush_i[3]),
    .data_i(mid_data_i[3]), .cfg_i(mid_cfg_i[3]), .mask_i(mid_mask_i[3]),
    .y_o(mid_y_o[3]), .meta_o(mid_meta_o[3]), .state_o(mid_state_o[3]), .valid_o(mid_valid_o[3])
  );

  sg_bank_cluster i_cluster (
    .clk(clk),
    .rst_n(rst_n),
    .cyc_i(cyc),
    .stim_a(stim_a),
    .stim_b(stim_b),
    .stim_c(stim_c),
    .src_y_i(mid_y_o),
    .src_meta_i(mid_meta_o),
    .src_state_i(mid_state_o),
    .src_valid_i(mid_valid_o),
    .y_o(dst_y_o),
    .meta_o(dst_meta_o),
    .state_o(dst_state_o),
    .valid_o(dst_valid_o)
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
    rst_n <= (cyc >= 3) && !((cyc >= 82) && (cyc < 85));
    stim_a <= lfsr64(stim_a) ^ {stim_b[31:0], stim_b[63:32]} ^ {32'(cyc * 5), 32'(cyc * 13)};
    stim_b <= lfsr64(stim_b ^ 64'hc001_cafe_5eed_f00d) + {stim_a[23:0], stim_a[63:24]};
    stim_c <= {stim_c[30:0], stim_c[31] ^ stim_c[21] ^ stim_c[1] ^ stim_c[0]} ^ 32'(cyc * 31);

    if ((cyc > 12) && !((cyc >= 82) && (cyc < 88))) crc <= crc32_bits(crc, sample);

    if (cyc == 250) begin
      $write("crc=%08x\n", crc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_bank_cluster (
  input  logic              clk,
  input  logic              rst_n,
  input  int                cyc_i,
  input  logic [63:0]       stim_a,
  input  logic [63:0]       stim_b,
  input  logic [31:0]       stim_c,
  input  logic [3:0][63:0]  src_y_i,
  input  logic [3:0][15:0]  src_meta_i,
  input  logic [3:0][2:0]   src_state_i,
  input  logic [3:0]        src_valid_i,
  output logic [3:0][63:0]  y_o,
  output logic [3:0][15:0]  meta_o,
  output logic [3:0][2:0]   state_o,
  output logic [3:0]        valid_o
);

  logic [3:0]        valid_i;
  logic [3:0]        hold_i;
  logic [3:0]        flush_i;
  logic [3:0][63:0]  data_i;
  logic [3:0][15:0]  cfg_i;
  logic [3:0][7:0]   mask_i;

  generate
    for (genvar g = 0; g < 4; g++) begin : gen_in
      localparam int A = g;
      localparam int B = (g + 1) % 4;
      localparam int C = (g + 2) % 4;
      assign valid_i[g] = rst_n && src_valid_i[A] && src_valid_i[B] && (((cyc_i + g) % 6) != 4);
      assign hold_i[g] = (((cyc_i + g + 1) & 7) == 2);
      assign flush_i[g] = rst_n && (((cyc_i + g) % 23) == 11);
      assign data_i[g] = src_y_i[A] + {src_meta_i[B], src_y_i[B][47:0]} + {src_y_i[C][31:0], stim_c};
      assign cfg_i[g] = src_meta_i[A] ^ src_meta_i[C] ^ {13'b0, src_state_i[B]};
      assign mask_i[g] = src_y_i[A][15:8] ^ src_y_i[B][7:0] ^ src_y_i[C][23:16] ^ 8'(cyc_i + (g * 9));
    end
  endgenerate

  sg_bank_node #(.P_W(24), .P_BANKS(1), .P_ALT(0), .P_SEED(32'h243f_6a88), .P_BIAS(8'h1b)) i_dst0 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[0]), .hold_i(hold_i[0]), .flush_i(flush_i[0]),
    .data_i(data_i[0]), .cfg_i(cfg_i[0]), .mask_i(mask_i[0]),
    .y_o(y_o[0]), .meta_o(meta_o[0]), .state_o(state_o[0]), .valid_o(valid_o[0])
  );
  sg_bank_node #(.P_W(40), .P_BANKS(2), .P_ALT(1), .P_SEED(32'h1319_8a2e), .P_BIAS(8'h2f)) i_dst1 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[1]), .hold_i(hold_i[1]), .flush_i(flush_i[1]),
    .data_i(data_i[1]), .cfg_i(cfg_i[1]), .mask_i(mask_i[1]),
    .y_o(y_o[1]), .meta_o(meta_o[1]), .state_o(state_o[1]), .valid_o(valid_o[1])
  );
  sg_bank_node #(.P_W(56), .P_BANKS(2), .P_ALT(0), .P_SEED(32'h5bd1_e995), .P_BIAS(8'h47)) i_dst2 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[2]), .hold_i(hold_i[2]), .flush_i(flush_i[2]),
    .data_i(data_i[2]), .cfg_i(cfg_i[2]), .mask_i(mask_i[2]),
    .y_o(y_o[2]), .meta_o(meta_o[2]), .state_o(state_o[2]), .valid_o(valid_o[2])
  );
  sg_bank_node #(.P_W(48), .P_BANKS(2), .P_ALT(1), .P_SEED(32'h0f1e_2d3c), .P_BIAS(8'h53)) i_dst3 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[3]), .hold_i(hold_i[3]), .flush_i(flush_i[3]),
    .data_i(data_i[3]), .cfg_i(cfg_i[3]), .mask_i(mask_i[3]),
    .y_o(y_o[3]), .meta_o(meta_o[3]), .state_o(state_o[3]), .valid_o(valid_o[3])
  );

endmodule

module sg_bank_node #(
  parameter int unsigned P_W = 32,
  parameter int unsigned P_BANKS = 1,
  parameter bit          P_ALT = 0,
  parameter logic [31:0] P_SEED = 32'h243f_6a88,
  parameter logic [7:0]  P_BIAS = 8'h1b
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic        hold_i,
  input  logic        flush_i,
  input  logic [63:0] data_i,
  input  logic [15:0] cfg_i,
  input  logic [7:0]  mask_i,
  output logic [63:0] y_o,
  output logic [15:0] meta_o,
  output logic [2:0]  state_o,
  output logic        valid_o
); /*verilator subgraph_boundary*/

  logic [P_W-1:0] bank0_q [0:3];
  logic [P_W-1:0] bank1_q [0:3];
  logic [P_W-1:0] read_mix;
  logic [P_W-1:0] write_mix;
  logic [63:0]    fold_mix;
  logic [63:0]    aux_mix;
  logic [31:0]    acc_q;
  logic [63:0]    y_q;
  logic [15:0]    meta_q;
  logic [2:0]     state_q;
  logic [1:0]     wr_ptr_q;
  logic [1:0]     rd_ptr_q;
  logic [1:0]     scrub_ptr_q;
  logic           bank_sel_q;
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

  function automatic logic [P_W-1:0] seedw(input logic [31:0] v);
    return P_W'(v);
  endfunction

  generate
    if (P_BANKS == 1) begin : gen_single
      always_comb begin
        read_mix = bank0_q[rd_ptr_q] ^ bank0_q[rd_ptr_q ^ 2'b01] ^ clipw({48'b0, cfg_i});
        write_mix = bank0_q[wr_ptr_q] ^ clipw(data_i) ^ clipw({32'b0, acc_q});
        fold_mix = zext64(bank0_q[0]) ^ {zext64(bank0_q[1])[31:0], zext64(bank0_q[2])[31:0]};
        aux_mix = zext64(bank0_q[3]) + {32'b0, acc_q} + {48'b0, cfg_i};
        if (P_ALT) begin
          read_mix ^= clipw({56'b0, mask_i});
          write_mix ^= clipw({48'b0, cfg_i});
          fold_mix ^= {data_i[23:0], data_i[63:24]};
        end else begin
          read_mix ^= clipw({32'b0, data_i[31:0]});
          write_mix ^= clipw({56'b0, P_BIAS});
          aux_mix ^= {56'b0, mask_i};
        end
      end

      always @(posedge clk) begin
        if (!rst_n) begin
          bank0_q[0] <= P_W'(P_SEED);
          bank0_q[1] <= P_W'(P_SEED ^ 32'h9e37_79b9);
          bank0_q[2] <= P_W'(P_SEED ^ 32'h3c6e_f372);
          bank0_q[3] <= P_W'(P_SEED ^ 32'ha54f_f53a);
        end else if (flush_i) begin
          bank0_q[cfg_i[1:0]] <= P_W'(P_SEED ^ {24'b0, mask_i});
        end else if (valid_i) begin
          bank0_q[wr_ptr_q] <= write_mix;
          if (!hold_i) bank0_q[rd_ptr_q] <= bank0_q[rd_ptr_q] ^ read_mix;
        end else if (!hold_i) begin
          bank0_q[scrub_ptr_q] <= bank0_q[scrub_ptr_q] + clipw(aux_mix);
        end
      end

      always @(posedge clk) begin
        if (!rst_n) bank1_q[0] <= '0;
        else bank1_q[0] <= bank1_q[0];
      end
    end else begin : gen_dual
      always_comb begin
        logic [P_W-1:0] lhs;
        logic [P_W-1:0] rhs;
        lhs = bank_sel_q ? bank1_q[rd_ptr_q] : bank0_q[rd_ptr_q];
        rhs = bank_sel_q ? bank0_q[rd_ptr_q ^ 2'b01] : bank1_q[rd_ptr_q ^ 2'b01];
        read_mix = lhs ^ rhs ^ clipw({48'b0, cfg_i});
        write_mix = (bank_sel_q ? bank1_q[wr_ptr_q] : bank0_q[wr_ptr_q]) ^ clipw(data_i);
        write_mix ^= clipw({32'b0, acc_q}) ^ clipw({56'b0, mask_i});
        fold_mix = zext64(bank0_q[0] ^ bank1_q[0]) ^ {zext64(bank0_q[1])[31:0], zext64(bank1_q[1])[31:0]};
        aux_mix = zext64(bank0_q[2] ^ bank1_q[2]) + zext64(bank0_q[3] ^ bank1_q[3]) + {48'b0, cfg_i};
        if (P_ALT) begin
          read_mix ^= clipw({56'b0, P_BIAS});
          fold_mix ^= {data_i[15:0], data_i[63:16]};
        end else begin
          write_mix ^= clipw({48'b0, cfg_i});
          aux_mix ^= {32'b0, data_i[31:0]};
        end
      end

      always @(posedge clk) begin
        if (!rst_n) begin
          bank0_q[0] <= P_W'(P_SEED);
          bank0_q[1] <= P_W'(P_SEED ^ 32'h9e37_79b9);
          bank0_q[2] <= P_W'(P_SEED ^ 32'h3c6e_f372);
          bank0_q[3] <= P_W'(P_SEED ^ 32'ha54f_f53a);
          bank1_q[0] <= seedw(~P_SEED);
          bank1_q[1] <= seedw((~P_SEED) ^ 32'h517c_c1b7);
          bank1_q[2] <= seedw((~P_SEED) ^ 32'h1f83_d9ab);
          bank1_q[3] <= seedw((~P_SEED) ^ 32'h5be0_cd19);
        end else if (flush_i) begin
          if (mask_i[0]) bank0_q[cfg_i[1:0]] <= P_W'(P_SEED ^ {24'b0, mask_i});
          else bank1_q[cfg_i[1:0]] <= seedw((~P_SEED) ^ {24'b0, mask_i});
        end else if (valid_i) begin
          if (bank_sel_q) bank1_q[wr_ptr_q] <= write_mix;
          else bank0_q[wr_ptr_q] <= write_mix;
          if (!hold_i) begin
            if (bank_sel_q) bank0_q[rd_ptr_q] <= bank0_q[rd_ptr_q] ^ read_mix;
            else bank1_q[rd_ptr_q] <= bank1_q[rd_ptr_q] + read_mix;
          end
        end else if (!hold_i) begin
          bank0_q[scrub_ptr_q] <= bank0_q[scrub_ptr_q] ^ clipw(aux_mix);
          bank1_q[scrub_ptr_q] <= bank1_q[scrub_ptr_q] + clipw(fold_mix);
        end
      end
    end
  endgenerate

  always @(posedge clk) begin
    if (!rst_n) begin
      wr_ptr_q <= 2'b00;
      rd_ptr_q <= 2'b01;
      scrub_ptr_q <= 2'b10;
      bank_sel_q <= 1'b0;
      valid_q <= 1'b0;
    end else begin
      if (valid_i) begin
        wr_ptr_q <= wr_ptr_q + 2'b01;
        rd_ptr_q <= rd_ptr_q + 2'b11;
      end
      if (!hold_i) scrub_ptr_q <= scrub_ptr_q + 2'b01;
      if (flush_i) bank_sel_q <= mask_i[0];
      else if (valid_i) bank_sel_q <= ~bank_sel_q;
      valid_q <= valid_i;
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      acc_q <= P_SEED ^ {24'b0, P_BIAS};
      y_q <= {32'h6a09_e667, P_SEED};
      meta_q <= P_SEED[15:0] ^ {8'b0, P_BIAS};
      state_q <= {P_BANKS > 1, P_ALT, 1'b0};
    end else begin
      if (flush_i) acc_q <= acc_q ^ {24'b0, mask_i} ^ {16'b0, cfg_i};
      else if (valid_i) acc_q <= {acc_q[15:0], acc_q[31:16]} ^ data_i[31:0] ^ {16'b0, cfg_i};
      else acc_q <= acc_q + {24'b0, P_BIAS} + {24'b0, mask_i};

      y_q <= fold_mix ^ aux_mix ^ {acc_q, 8'b0, cfg_i, mask_i};
      meta_q <= cfg_i ^ acc_q[15:0] ^ {8'b0, mask_i};
      state_q <= {bank_sel_q, flush_i, hold_i} ^ {P_BANKS > 1, P_ALT, valid_i};
    end
  end

  assign y_o = y_q;
  assign meta_o = meta_q;
  assign state_o = state_q;
  assign valid_o = valid_q;

endmodule
