// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// Test: nested parameterized interface inside a types interface causes
//       $bits() to evaluate with wrong struct width.
//

package cfg3_pkg;
  typedef struct packed {
    int unsigned Capacity;
    int unsigned Slices;
    int unsigned NumThreads;
    int unsigned NumIds;
  } cfg_t;
endpackage

// Inner types interface (mirrors xyz_types_if).
// Provides types derived from cfg that the outer interface imports.
interface inner_types_if #(
  parameter cfg3_pkg::cfg_t cfg = '0
) ();
  typedef logic [$clog2(cfg.NumIds)-1:0] trans_id_t;
  typedef logic [$clog2(cfg.NumThreads)-1:0] tl_index_t;
endinterface

// Outer types interface (mirrors smem_types_if).
// Instantiates inner_types_if, imports types from it, and builds
// compound struct typedefs that include those imported types.
interface outer_types_if #(
  parameter cfg3_pkg::cfg_t cfg = '0
) ();
  localparam int NUM_ROWS = (cfg.Capacity / cfg.Slices) / 8;
  typedef logic [$clog2(NUM_ROWS)-1:0] row_addr_t;

  // Nested interface - this is the trigger.
  inner_types_if #(cfg) inner_types();
  typedef inner_types.trans_id_t trans_id_t;
  typedef inner_types.tl_index_t tl_index_t;

  typedef logic [$clog2(cfg.NumThreads)-1:0] pkt_nid_t;

  typedef struct packed {
    pkt_nid_t src_nid;
    pkt_nid_t dst_nid;
  } pkt_hdr_t;

  typedef union packed {
    logic [$bits(row_addr_t)+$bits(tl_index_t)+6-1:0] raw;
    struct packed {
      row_addr_t row_index;
      tl_index_t tl_index;
      logic [5:0] bit_index;
    } fld;
  } addr_t;

  typedef struct packed {
    logic       en;
    trans_id_t  tag;
    tl_index_t  tl;
    logic       is_read;
    logic       needs_resp;
  } meta_t;

  typedef struct packed {
    meta_t  meta;
    addr_t  addr;
    logic [63:0] data;
  } rq_t;

  // Compound packet type (mirrors iq_pkt_t)
  typedef struct packed {
    pkt_hdr_t hdr;
    rq_t      payload;
  } pkt_t;
endinterface

// Width-parameterized FIFO (mirrors ring_fifo).
module fifo3 #(
  parameter int p_width = 1,
  parameter int p_depth = 2
) (
  input  logic clk,
  input  logic rst_n,
  input  logic [p_width-1:0] push_dat_i,
  input  logic push_vld_i,
  output logic [p_width-1:0] front_dat_o,
  output logic not_empty_o
);
  logic [p_width-1:0] mem [p_depth];
  logic [$clog2(p_depth)-1:0] wptr, rptr;
  logic [p_depth:0] count;
  assign not_empty_o = (count != 0);
  assign front_dat_o = mem[rptr];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wptr <= '0;
      rptr <= '0;
      count <= '0;
    end else if (push_vld_i) begin
      mem[wptr] <= push_dat_i;
      wptr <= wptr + 1;
      count <= count + 1;
    end
  end
endmodule

// Slice module (mirrors smem_slice).
// Receives iq_pkt_t as a TYPE PARAMETER from wrapper3, then uses
// $bits(iq_pkt_t) as a value parameter to fifo3.
// This forces $bits() evaluation during widthParamsEdit of the slice3
// cell (in wrapper3's cell loop), before outer_types_if__Az1's nested
// inner_types_if is deparameterized.
module slice3 #(
  parameter cfg3_pkg::cfg_t cfg = '0,
  parameter int SLICE_IDX = 0,
  parameter type iq_pkt_t = logic,
  parameter type oq_pkt_t = logic
) (
  input  logic clk,
  input  logic rst_n,
  input  logic in_vld,
  output logic out_vld,
  output iq_pkt_t fe_ot_pkt_o
);
  // Local outer_types_if for other local types
  outer_types_if #(cfg) types();
  typedef types.pkt_nid_t pkt_nid_t;

  iq_pkt_t rqq_in, rqq_ot;
  logic rqq_ot_vld;

  assign rqq_in.hdr.src_nid = pkt_nid_t'(SLICE_IDX);
  assign rqq_in.hdr.dst_nid = '0;
  assign rqq_in.payload.meta.en = in_vld;
  assign rqq_in.payload.meta.tag = '0;
  assign rqq_in.payload.meta.tl = '0;
  assign rqq_in.payload.meta.is_read = 1'b1;
  assign rqq_in.payload.meta.needs_resp = 1'b0;
  assign rqq_in.payload.addr = '0;
  assign rqq_in.payload.data = 64'hCAFE_BABE;

  // $bits(iq_pkt_t) as value parameter - the bug trigger.
  // iq_pkt_t is a type parameter whose PARAMTYPEDTYPE child REFDTYPE
  // points into the outer_types_if clone's STRUCTDTYPE.  When
  // widthParamsEdit evaluates this during wrapper3's cell loop,
  // the nested inner_types_if inside outer_types_if__Az1 hasn't
  // been deparameterized, so trans_id_t/tl_index_t have wrong widths.
  fifo3 #(
    .p_width($bits(iq_pkt_t)),
    .p_depth(4)
  ) rqq (
    .clk(clk),
    .rst_n(rst_n),
    .push_dat_i(rqq_in),
    .push_vld_i(in_vld),
    .front_dat_o(rqq_ot),
    .not_empty_o(rqq_ot_vld)
  );

  assign fe_ot_pkt_o = rqq_ot;
  assign out_vld = rqq_ot_vld;
endmodule

// Wrapper module (mirrors smem_top).
// Creates outer_types_if, imports pkt_t, and passes it as a type
// parameter to slice3 instances in a generate loop.
module wrapper3 #(
  parameter cfg3_pkg::cfg_t cfg = '0
) (
  input  logic clk,
  input  logic rst_n
);
  outer_types_if #(cfg) types();
  typedef types.pkt_t iq_pkt_t;
  typedef types.rq_t  oq_pkt_t;

  // Capture $bits of the type parameter for external checking.
  // If the nested inner_types_if hasn't been deparameterized before
  // this is evaluated, the width will be wrong (e.g. 90 instead of 92).
  localparam int PKT_WIDTH = $bits(iq_pkt_t);

  logic [cfg.NumThreads-1:0] out_vld;

  generate
    for (genvar i = 0; i < cfg.NumThreads; i++) begin : gen_slices
      iq_pkt_t fe_pkt;
      slice3 #(
        .cfg(cfg),
        .SLICE_IDX(i),
        .iq_pkt_t(iq_pkt_t),
        .oq_pkt_t(oq_pkt_t)
      ) u_slice (
        .clk(clk),
        .rst_n(rst_n),
        .in_vld(1'b1),
        .out_vld(out_vld[i]),
        .fe_ot_pkt_o(fe_pkt)
      );
    end
  endgenerate
endmodule

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  logic rst_n = 0;

  int cyc = 0;

  localparam cfg3_pkg::cfg_t MY_CFG = '{
    Capacity: 8192,
    Slices: 8,
    NumThreads: 4,
    NumIds: 16
  };
  // Expected widths:
  //   trans_id_t = $clog2(16) = 4 bits
  //   tl_index_t = $clog2(4)  = 2 bits
  //   row_addr_t = $clog2((8192/8)/8) = $clog2(128) = 7 bits
  //   pkt_nid_t  = $clog2(4) = 2 bits
  //   pkt_hdr_t  = 2+2 = 4 bits
  //   addr_t     = 7+2+6 = 15 bits
  //   meta_t     = 1+4+2+1+1 = 9 bits
  //   rq_t       = 9+15+64 = 88 bits
  //   pkt_t      = 4+88 = 92 bits

  // Compute expected pkt_t width from first principles.
  // These computations happen in the testbench module context where
  // the cfg parameter values are known constants, not through the
  // nested interface PARAMTYPEDTYPE chain.
  localparam int EXP_TRANS_ID_W = $clog2(MY_CFG.NumIds);       // 4
  localparam int EXP_TL_INDEX_W = $clog2(MY_CFG.NumThreads);   // 2
  localparam int EXP_ROW_ADDR_W = $clog2((MY_CFG.Capacity / MY_CFG.Slices) / 8); // 7
  localparam int EXP_PKT_NID_W  = $clog2(MY_CFG.NumThreads);   // 2
  localparam int EXP_PKT_HDR_W  = 2 * EXP_PKT_NID_W;           // 4
  localparam int EXP_ADDR_W     = EXP_ROW_ADDR_W + EXP_TL_INDEX_W + 6; // 15
  localparam int EXP_META_W     = 1 + EXP_TRANS_ID_W + EXP_TL_INDEX_W + 1 + 1; // 9
  localparam int EXP_RQ_W       = EXP_META_W + EXP_ADDR_W + 64; // 88
  localparam int EXP_PKT_W      = EXP_PKT_HDR_W + EXP_RQ_W;    // 92

  wrapper3 #(.cfg(MY_CFG)) u_wrapper (
    .clk(clk),
    .rst_n(rst_n)
  );

  // Self-check: verify that $bits(pkt_t) as seen through the nested
  // interface type parameter chain matches the expected width.
  // If the bug is present, u_wrapper.PKT_WIDTH will be < EXP_PKT_W
  // because trans_id_t was evaluated with the template default
  // cfg.NumIds=0 instead of the actual value 16.
  initial begin
    if (u_wrapper.PKT_WIDTH != EXP_PKT_W) begin
      $display("%%Error: t_iface_nested_width3.v: $bits(pkt_t) = %0d, expected %0d", u_wrapper.PKT_WIDTH, EXP_PKT_W);
      $stop;
    end
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) rst_n <= 1;
    if (cyc > 5) begin
      if (u_wrapper.out_vld !== {MY_CFG.NumThreads{1'b1}}) begin
        $display("FAIL cyc=%0d: out_vld=%b", cyc, u_wrapper.out_vld);
        $stop;
      end
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
