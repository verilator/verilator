// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

module t (
  input logic clk
);

  localparam int N_TOP = 6;
  localparam int N_CLUSTER = 4;
  localparam int N_TOTAL = N_TOP + N_CLUSTER;
  localparam int SAMPLE_BITS = N_TOTAL * (64 + 16 + 1 + 3);

  logic [6:0] independent_count;
  sg_slice_independent i_independent (.clk(clk), .q(independent_count));

  int cyc;
  logic rst_n;
  logic [63:0] stim_a;
  logic [63:0] stim_b;
  logic [31:0] stim_c;
  logic [31:0] crc;

  logic [N_TOP-1:0]        top_valid_i;
  logic [N_TOP-1:0]        top_hold_i;
  logic [N_TOP-1:0]        top_flush_i;
  logic [N_TOP-1:0][63:0]  top_data_i;
  logic [N_TOP-1:0][63:0]  top_aux_i;
  logic [N_TOP-1:0][15:0]  top_cfg_i;
  logic [N_TOP-1:0][7:0]   top_mask_i;
  logic [N_TOP-1:0][63:0]  top_y_o;
  logic [N_TOP-1:0][15:0]  top_meta_o;
  logic [N_TOP-1:0][2:0]   top_state_o;
  logic [N_TOP-1:0]        top_valid_o;

  logic [N_CLUSTER-1:0][63:0] cl_y_o;
  logic [N_CLUSTER-1:0][15:0] cl_meta_o;
  logic [N_CLUSTER-1:0][2:0]  cl_state_o;
  logic [N_CLUSTER-1:0]       cl_valid_o;

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
      localparam logic [15:0] K16 = 16'h6d21 ^ (16'h1049 * (g + 5));
      assign top_valid_i[g] = rst_n && (((cyc + g) % 5) != 1);
      assign top_hold_i[g] = (((cyc + g) & 3) == 2) ^ (((cyc + g) % 11) == 5);
      assign top_flush_i[g] = rst_n && ((((cyc + g) % 7) == 3) || (((cyc + g) % 13) == 4));
      assign top_data_i[g] = stim_a ^ {stim_c, ~stim_c} ^ K64 ^ (64'(cyc + 7) << (g % 11));
      assign top_aux_i[g] = stim_b + {stim_c, 32'(cyc * (g + 9))} + {48'b0, K16};
      assign top_cfg_i[g] = stim_b[15:0] ^ K16 ^ 16'(cyc * (g + 3));
      assign top_mask_i[g] = stim_a[7:0] ^ stim_b[23:16] ^ 8'(cyc + (g * 8'h1d));
      assign sample[(g*(64+16+1+3)) +: (64+16+1+3)] = {top_valid_o[g], top_state_o[g], top_meta_o[g], top_y_o[g]};
    end
  endgenerate

  sg_slice_node #(.P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h19)) i_top0 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[0]), .hold_i(top_hold_i[0]), .flush_i(top_flush_i[0]),
    .data_i(top_data_i[0]), .aux_i(top_aux_i[0]), .cfg_i(top_cfg_i[0]), .mask_i(top_mask_i[0]),
    .y_o(top_y_o[0]), .meta_o(top_meta_o[0]), .state_o(top_state_o[0]), .valid_o(top_valid_o[0])
  );
  sg_slice_node #(.P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h19)) i_top1 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[1]), .hold_i(top_hold_i[1]), .flush_i(top_flush_i[1]),
    .data_i(top_data_i[1]), .aux_i(top_aux_i[1]), .cfg_i(top_cfg_i[1]), .mask_i(top_mask_i[1]),
    .y_o(top_y_o[1]), .meta_o(top_meta_o[1]), .state_o(top_state_o[1]), .valid_o(top_valid_o[1])
  );
  sg_slice_node #(.P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h2f)) i_top2 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[2]), .hold_i(top_hold_i[2]), .flush_i(top_flush_i[2]),
    .data_i(top_data_i[2]), .aux_i(top_aux_i[2]), .cfg_i(top_cfg_i[2]), .mask_i(top_mask_i[2]),
    .y_o(top_y_o[2]), .meta_o(top_meta_o[2]), .state_o(top_state_o[2]), .valid_o(top_valid_o[2])
  );
  sg_slice_node #(.P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h2f)) i_top3 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[3]), .hold_i(top_hold_i[3]), .flush_i(top_flush_i[3]),
    .data_i(top_data_i[3]), .aux_i(top_aux_i[3]), .cfg_i(top_cfg_i[3]), .mask_i(top_mask_i[3]),
    .y_o(top_y_o[3]), .meta_o(top_meta_o[3]), .state_o(top_state_o[3]), .valid_o(top_valid_o[3])
  );
  sg_slice_node #(.P_ALT(0), .P_TAG(16'h6b8d), .P_BIAS(8'h43)) i_top4 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[4]), .hold_i(top_hold_i[4]), .flush_i(top_flush_i[4]),
    .data_i(top_data_i[4]), .aux_i(top_aux_i[4]), .cfg_i(top_cfg_i[4]), .mask_i(top_mask_i[4]),
    .y_o(top_y_o[4]), .meta_o(top_meta_o[4]), .state_o(top_state_o[4]), .valid_o(top_valid_o[4])
  );
  sg_slice_node #(.P_ALT(1), .P_TAG(16'h7f43), .P_BIAS(8'h57)) i_top5 (
    .clk(clk), .rst_n(rst_n), .valid_i(top_valid_i[5]), .hold_i(top_hold_i[5]), .flush_i(top_flush_i[5]),
    .data_i(top_data_i[5]), .aux_i(top_aux_i[5]), .cfg_i(top_cfg_i[5]), .mask_i(top_mask_i[5]),
    .y_o(top_y_o[5]), .meta_o(top_meta_o[5]), .state_o(top_state_o[5]), .valid_o(top_valid_o[5])
  );

  sg_slice_cluster i_cluster (
    .clk(clk),
    .rst_n(rst_n),
    .cyc_i(cyc),
    .stim_a(stim_a),
    .stim_b(stim_b),
    .stim_c(stim_c),
    .src_y_i(top_y_o),
    .src_meta_i(top_meta_o),
    .src_state_i(top_state_o),
    .src_valid_i(top_valid_o),
    .y_o(cl_y_o),
    .meta_o(cl_meta_o),
    .state_o(cl_state_o),
    .valid_o(cl_valid_o)
  );

  generate
    for (genvar g = 0; g < N_CLUSTER; g++) begin : gen_cl
      assign sample[((N_TOP+g)*(64+16+1+3)) +: (64+16+1+3)] = {cl_valid_o[g], cl_state_o[g], cl_meta_o[g], cl_y_o[g]};
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
    if (independent_count != 7'(cyc)) $stop;
    cyc <= cyc + 1;
    rst_n <= (cyc >= 3) && !((cyc >= 80) && (cyc < 83));
    stim_a <= lfsr64(stim_a) ^ {stim_b[31:0], stim_b[63:32]} ^ {32'(cyc * 11), 32'(cyc * 17)};
    stim_b <= lfsr64(stim_b ^ 64'hc001_cafe_5eed_f00d) + {stim_a[23:0], stim_a[63:24]};
    stim_c <= {stim_c[30:0], stim_c[31] ^ stim_c[21] ^ stim_c[1] ^ stim_c[0]} ^ 32'(cyc * 37);

    if ((cyc > 12) && !((cyc >= 80) && (cyc < 86))) crc <= crc32_bits(crc, sample);

    if (cyc == 250) begin
      $write("crc=%08x\n", crc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_slice_cluster (
  input  logic              clk,
  input  logic              rst_n,
  input  int                cyc_i,
  input  logic [63:0]       stim_a,
  input  logic [63:0]       stim_b,
  input  logic [31:0]       stim_c,
  input  logic [5:0][63:0]  src_y_i,
  input  logic [5:0][15:0]  src_meta_i,
  input  logic [5:0][2:0]   src_state_i,
  input  logic [5:0]        src_valid_i,
  output logic [3:0][63:0]  y_o,
  output logic [3:0][15:0]  meta_o,
  output logic [3:0][2:0]   state_o,
  output logic [3:0]        valid_o
);
  logic [3:0]        valid_i;
  logic [3:0]        hold_i;
  logic [3:0]        flush_i;
  logic [3:0][63:0]  data_i;
  logic [3:0][63:0]  aux_i;
  logic [3:0][15:0]  cfg_i;
  logic [3:0][7:0]   mask_i;

  generate
    for (genvar g = 0; g < 4; g++) begin : gen_in
      localparam int A = g;
      localparam int B = g + 2;
      assign valid_i[g] = rst_n && src_valid_i[A] && (((cyc_i + g) % 6) != 2);
      assign hold_i[g] = (((cyc_i + g) % 5) == 1) ^ (((cyc_i + g) % 9) == 4);
      assign flush_i[g] = rst_n && ((((cyc_i + g) % 8) == 3) || (((cyc_i + g) % 14) == 6));
      assign data_i[g] = src_y_i[A] ^ {src_meta_i[B], src_y_i[B][47:0]} ^ stim_a;
      assign aux_i[g] = src_y_i[B] + {src_meta_i[A], src_y_i[A][47:0]} + stim_b;
      assign cfg_i[g] = src_meta_i[A] ^ src_meta_i[B] ^ {13'b0, src_state_i[A]};
      assign mask_i[g] = src_y_i[A][7:0] ^ src_y_i[B][15:8] ^ 8'(cyc_i + (g * 13));
    end
  endgenerate

  sg_slice_node #(.P_ALT(0), .P_TAG(16'h3141), .P_BIAS(8'h19)) i_c0 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[0]), .hold_i(hold_i[0]), .flush_i(flush_i[0]),
    .data_i(data_i[0]), .aux_i(aux_i[0]), .cfg_i(cfg_i[0]), .mask_i(mask_i[0]),
    .y_o(y_o[0]), .meta_o(meta_o[0]), .state_o(state_o[0]), .valid_o(valid_o[0])
  );
  sg_slice_node #(.P_ALT(1), .P_TAG(16'h52c3), .P_BIAS(8'h2f)) i_c1 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[1]), .hold_i(hold_i[1]), .flush_i(flush_i[1]),
    .data_i(data_i[1]), .aux_i(aux_i[1]), .cfg_i(cfg_i[1]), .mask_i(mask_i[1]),
    .y_o(y_o[1]), .meta_o(meta_o[1]), .state_o(state_o[1]), .valid_o(valid_o[1])
  );
  sg_slice_node #(.P_ALT(0), .P_TAG(16'h6b8d), .P_BIAS(8'h43)) i_c2 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[2]), .hold_i(hold_i[2]), .flush_i(flush_i[2]),
    .data_i(data_i[2]), .aux_i(aux_i[2]), .cfg_i(cfg_i[2]), .mask_i(mask_i[2]),
    .y_o(y_o[2]), .meta_o(meta_o[2]), .state_o(state_o[2]), .valid_o(valid_o[2])
  );
  sg_slice_node #(.P_ALT(1), .P_TAG(16'h7f43), .P_BIAS(8'h57)) i_c3 (
    .clk(clk), .rst_n(rst_n), .valid_i(valid_i[3]), .hold_i(hold_i[3]), .flush_i(flush_i[3]),
    .data_i(data_i[3]), .aux_i(aux_i[3]), .cfg_i(cfg_i[3]), .mask_i(mask_i[3]),
    .y_o(y_o[3]), .meta_o(meta_o[3]), .state_o(state_o[3]), .valid_o(valid_o[3])
  );

endmodule

module sg_slice_node #(
  parameter bit          P_ALT = 0,
  parameter logic [15:0] P_TAG = 16'h3141,
  parameter logic [7:0]  P_BIAS = 8'h19
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        valid_i,
  input  logic        hold_i,
  input  logic        flush_i,
  input  logic [63:0] data_i,
  input  logic [63:0] aux_i,
  input  logic [15:0] cfg_i,
  input  logic [7:0]  mask_i,
  output logic [63:0] y_o,
  output logic [15:0] meta_o,
  output logic [2:0]  state_o,
  output logic        valid_o
); /*verilator subgraph_boundary*/

  logic [127:0] wide_q;
  logic [63:0]  low_mix;
  logic [63:0]  high_mix;
  logic [31:0]  acc_q;
  logic [63:0]  y_q;
  logic [15:0]  meta_q;
  logic [2:0]   state_q;
  logic         valid_q;

  always_comb begin
    low_mix = wide_q[63:0] ^ data_i ^ {48'b0, cfg_i};
    high_mix = wide_q[127:64] ^ aux_i ^ {56'b0, mask_i};
    if (P_ALT) begin
      low_mix ^= {aux_i[23:0], aux_i[63:24]};
      high_mix += {data_i[15:0], data_i[63:16]};
    end else begin
      low_mix += {data_i[23:0], data_i[63:24]};
      high_mix ^= {aux_i[15:0], aux_i[63:16]};
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      wide_q <= {64'h6a09_e667_f3bc_c908, 32'hbb67_ae85, 16'h1f83, P_TAG};
      acc_q <= {16'h510e, P_TAG};
      valid_q <= 1'b0;
    end else begin
      valid_q <= valid_i;
      if (flush_i && valid_i && hold_i) begin
        wide_q[127:96] <= data_i[31:0] ^ acc_q;
        wide_q[95:64] <= aux_i[31:0] ^ {16'b0, cfg_i};
        wide_q[63:48] <= cfg_i ^ {8'b0, mask_i};
        wide_q[47:0] <= wide_q[47:0] ^ {32'b0, cfg_i};
        acc_q <= acc_q ^ data_i[31:0] ^ aux_i[31:0];
      end else if (flush_i && valid_i) begin
        wide_q[127:64] <= high_mix;
        wide_q[63:32] <= data_i[31:0] ^ acc_q;
        wide_q[31:0] <= {16'b0, cfg_i} ^ {24'b0, mask_i};
        acc_q <= {acc_q[7:0], acc_q[31:8]} ^ aux_i[31:0];
      end else if (flush_i && hold_i) begin
        wide_q[127:96] <= aux_i[31:0] ^ acc_q;
        wide_q[95:64] <= wide_q[95:64] + {16'b0, cfg_i};
        wide_q[63:0] <= wide_q[63:0] ^ {56'b0, mask_i};
        acc_q <= acc_q + {24'b0, P_BIAS} + {16'b0, cfg_i};
      end else if (valid_i && hold_i) begin
        wide_q[127:64] <= high_mix;
        wide_q[63:32] <= low_mix[31:0] ^ acc_q;
        acc_q <= acc_q ^ data_i[31:0] ^ {24'b0, mask_i};
      end else if (valid_i) begin
        wide_q[127:64] <= high_mix;
        wide_q[63:0] <= low_mix;
        acc_q <= {acc_q[15:0], acc_q[31:16]} ^ data_i[31:0] ^ {16'b0, cfg_i};
      end else if (hold_i) begin
        wide_q[95:64] <= wide_q[95:64] ^ aux_i[31:0];
        wide_q[31:0] <= wide_q[31:0] + {24'b0, P_BIAS};
      end else begin
        wide_q[127:96] <= high_mix[31:0];
        wide_q[63:32] <= low_mix[31:0];
        acc_q <= acc_q + {24'b0, P_BIAS} + {24'b0, mask_i};
      end
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      y_q <= {32'h1f83_d9ab, 16'h0000, P_TAG};
      meta_q <= P_TAG ^ 16'h00f0;
      state_q <= {P_ALT, 2'b00};
    end else begin
      y_q <= wide_q[127:64] ^ wide_q[63:0] ^ {acc_q, cfg_i, mask_i, P_BIAS};
      meta_q <= cfg_i ^ acc_q[15:0] ^ wide_q[31:16];
      state_q <= {flush_i, hold_i, valid_i} ^ {P_ALT, 1'b0, 1'b1};
    end
  end

  assign y_o = y_q;
  assign meta_o = meta_q;
  assign state_o = state_q;
  assign valid_o = valid_q;

endmodule

// An independent boundary is scheduled alongside the connected slice network.
module sg_slice_independent (
  input logic clk,
  output logic [6:0] q = 0
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= q + 1'b1;
endmodule
