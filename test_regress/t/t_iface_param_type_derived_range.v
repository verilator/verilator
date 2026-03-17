// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// Test: struct typedef from parameterized interface with derived localparam
//       used as type parameter to a sub-module cell.
//
// Mirrors the Aerial smem_top → smem_slice → tflop_nr pattern:
//   1. types_if: parameterized interface with localparam derived from cfg
//      using division (0/0 = X on template default), used via $clog2 in
//      typedef range, and that typedef used inside a union/struct.
//   2. wrapper (smem_top): instantiates types_if, imports a compound type
//      (pkt_t), and passes it as a type parameter to slice.
//   3. slice (smem_slice): receives pkt_t as a type parameter from wrapper,
//      ALSO instantiates types_if locally, builds a local struct (rq_t)
//      from locally-imported types, and passes rq_t as a type parameter
//      to tflop_nr.
//   4. During deparameterization of tflop_nr inside the cloned slice,
//      widthParamsEdit follows the PARAMTYPEDTYPE chain back to the
//      template types_if's unresolved union (with X-valued range).

package cfg_pkg;
  typedef struct packed {
    int unsigned Capacity;
    int unsigned Slices;
    int unsigned NumThreads;
  } cfg_t;
endpackage

// Types interface: derives localparam from cfg, uses in typedef range,
// builds union/struct containing that typedef.
// On the template default (cfg='0), Capacity/Slices = 0/0 = X.
interface types_if #(
    parameter cfg_pkg::cfg_t cfg = '0
) ();
  localparam int NUM_ROWS = (cfg.Capacity / cfg.Slices) / 8;
  typedef logic [$clog2(NUM_ROWS)-1:0] row_addr_t;
  typedef logic [$clog2(cfg.NumThreads)-1:0] tl_addr_t;

  typedef union packed {
    logic [$bits(row_addr_t)+$bits(tl_addr_t)+6-1:0] raw;
    struct packed {
      row_addr_t row_index;
      tl_addr_t  tl_index;
      logic [5:0] bit_index;
    } fld;
  } addr_t;

  typedef struct packed {
    logic       en;
    logic [3:0] tag;
    logic       is_read;
  } meta_t;

  // Compound packet type (mirrors iq_pkt_t)
  typedef struct packed {
    meta_t  meta;
    addr_t  addr;
    logic [63:0] data;
  } pkt_t;
endinterface

// Generic type-parameterized register (mirrors tflop_nr)
module tflop_nr #(parameter type T = logic) (
    input  logic clk,
    input  logic rst_n,
    output T     q_o,
    input  T     d_i
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) q_o <= '0;
    else        q_o <= d_i;
  end
endmodule

// Slice module: receives pkt_t as type param from wrapper, also
// instantiates types_if locally, builds local struct from local types,
// passes that struct as type param to tflop_nr.
// (mirrors smem_slice)
module slice #(
    parameter cfg_pkg::cfg_t cfg = '0,
    parameter int SLICE_IDX = 0,
    parameter type pkt_t = logic
) (
    input  logic clk,
    input  logic rst_n,
    input  logic in_vld,
    input  pkt_t in_pkt,
    output logic out_vld,
    output pkt_t out_pkt
);
  // Local types_if instantiation — same cfg as wrapper's
  types_if #(cfg) types();

  typedef types.addr_t  addr_t;
  typedef types.meta_t  meta_t;

  // Local struct containing locally-imported interface types
  typedef struct packed {
    meta_t meta;
    addr_t addr;
  } rq_t;

  rq_t rq_d, rq_q;

  always_comb begin
    rq_d = rq_q;
    if (in_vld) begin
      rq_d.meta = in_pkt.meta;
      rq_d.addr = in_pkt.addr;
    end
  end

  // Pass local struct as type param to tflop_nr — this is the trigger
  tflop_nr #(.T(rq_t)) rq_reg (
      .clk(clk),
      .rst_n(rst_n),
      .q_o(rq_q),
      .d_i(rq_d)
  );

  assign out_vld = rq_q.meta.en;
  assign out_pkt.meta = rq_q.meta;
  assign out_pkt.addr = rq_q.addr;
  assign out_pkt.data = in_pkt.data;
endmodule

// Wrapper module: instantiates types_if, imports pkt_t, passes it as
// type param to slice instances in a generate loop.
// (mirrors smem_top)
module wrapper #(
    parameter cfg_pkg::cfg_t cfg = '0
) (
    input  logic clk,
    input  logic rst_n
);
  types_if #(cfg) types();

  typedef types.pkt_t pkt_t;
  typedef types.meta_t meta_t;

  pkt_t in_pkt;
  logic in_vld;

  assign in_vld = 1'b1;
  assign in_pkt.meta.en = 1'b1;
  assign in_pkt.meta.tag = 4'd5;
  assign in_pkt.meta.is_read = 1'b0;
  assign in_pkt.addr = '0;
  assign in_pkt.data = 64'hDEAD_BEEF;

  // Generate loop with slices (mirrors gen_slices in smem_top)
  logic [cfg.NumThreads-1:0] out_vld;
  pkt_t [cfg.NumThreads-1:0] out_pkt;

  generate
    for (genvar i = 0; i < 2; i++) begin : gen_slices
      slice #(
          .cfg(cfg),
          .SLICE_IDX(i),
          .pkt_t(pkt_t)
      ) u_slice (
          .clk(clk),
          .rst_n(rst_n),
          .in_vld(in_vld),
          .in_pkt(in_pkt),
          .out_vld(out_vld[i]),
          .out_pkt(out_pkt[i])
      );
    end
  endgenerate
endmodule

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  logic rst_n = 0;

  int cyc = 0;

  localparam cfg_pkg::cfg_t MY_CFG = '{
      Capacity: 8192,
      Slices: 8,
      NumThreads: 32
  };
  // Expected: NUM_ROWS = (8192/8)/8 = 128
  //           row_addr_t = logic [6:0]   (7 bits)
  //           tl_addr_t  = logic [4:0]   (5 bits)
  //           addr_t.raw = logic [17:0]  (7+5+6 = 18 bits)

  wrapper #(.cfg(MY_CFG)) u_wrapper (
      .clk(clk),
      .rst_n(rst_n)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) rst_n <= 1;
    if (cyc > 5) begin
      if (u_wrapper.out_vld[0] !== 1'b1) begin
        $display("FAIL cyc=%0d: out_vld[0]=%b expected 1", cyc, u_wrapper.out_vld[0]);
        $stop;
      end
      if (u_wrapper.out_pkt[0].meta.tag !== 4'd5) begin
        $display("FAIL cyc=%0d: tag=%0d expected 5", cyc, u_wrapper.out_pkt[0].meta.tag);
        $stop;
      end
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
