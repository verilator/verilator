// DESCRIPTION: Verilator: Test for interface typedef resolving to correct clone
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// When a non-parameterized wrapper module (#()) has multiple interface ports
// of the same parameterized interface type but with different configurations,
// typedefs extracted from those ports (e.g., typedef tgt_io.req_t local_t)
// must resolve to the struct from the CORRECT interface clone.
//
// This test models the aerial design hierarchy:
//   Path A: dw_converter_wrap#()(tgt_io[Id=2,Data=64], mst_io[Id=2,Data=128])
//           -> dw_converter -> dw_upsizer -> axi_demux -> axi_demux_simple
//   Path B: axi_to_axi_lite_wrap#()(axi_tgt_io[Id=8,Data=64])
//           -> axi_to_axi_lite -> axi_burst_splitter -> axi_demux -> axi_demux_simple
//
// Checks:
//   1. $bits of typedef'd types match the interface config (not a sibling clone)
//   2. Nested struct member access (slv_req_i.aw.id[0+:N]) extracts correct bits
//   3. Data written to interface ports arrives at leaf modules with correct values
//
// This file is ONLY for use with Verilator.

package cfg_pkg;
  typedef struct packed {
    int unsigned IdBits;
    int unsigned DataBits;
  } cfg_t;
endpackage

// Parameterized interface (like axi4_if)
interface my_if #(parameter cfg_pkg::cfg_t cfg = 0);
  typedef logic [cfg.IdBits-1:0]     id_t;
  typedef logic [cfg.DataBits-1:0]   data_t;
  typedef logic [cfg.DataBits/8-1:0] strb_t;

  typedef struct packed {
    id_t   id;
    data_t data;
    logic [7:0] len;
    logic [2:0] size;
    logic [1:0] burst;
  } aw_chan_t;

  typedef struct packed {
    data_t data;
    strb_t strb;
    logic  last;
  } w_chan_t;

  typedef struct packed {
    id_t      id;
    logic [1:0] resp;
  } b_chan_t;

  typedef struct packed {
    id_t   id;
    data_t data;
    logic [7:0] len;
    logic [2:0] size;
    logic [1:0] burst;
  } ar_chan_t;

  typedef struct packed {
    id_t      id;
    data_t    data;
    logic [1:0] resp;
    logic     last;
  } r_chan_t;

  typedef struct packed {
    aw_chan_t aw;
    logic     aw_valid;
    w_chan_t  w;
    logic     w_valid;
    logic     b_ready;
    ar_chan_t ar;
    logic     ar_valid;
    logic     r_ready;
  } req_t;

  typedef struct packed {
    logic     aw_ready;
    logic     w_ready;
    b_chan_t  b;
    logic     b_valid;
    r_chan_t  r;
    logic     r_valid;
  } resp_t;

  req_t  req;
  resp_t resp;

  modport target(input req, output resp);
  modport initiator(output req, input resp);
endinterface

//======================================================================
// Leaf: axi_demux_simple skeleton
//======================================================================
module axi_demux_simple #(
  parameter int unsigned AxiIdWidth  = 32'd0,
  parameter type         axi_req_t  = logic,
  parameter type         axi_resp_t = logic,
  parameter int unsigned AxiLookBits = 32'd3
)(
  input  logic     clk_i,
  input  logic     rst_ni,
  input  axi_req_t slv_req_i,
  output axi_resp_t slv_resp_o,
  output logic [AxiLookBits-1:0] id_out,
  output int unsigned req_bits_out
);
  // Extract ID from nested struct — triggers SELRANGE if axi_req_t
  // is from wrong interface clone (id field narrower than AxiLookBits)
  assign id_out = slv_req_i.aw.id[0+:AxiLookBits];
  assign slv_resp_o = '0;
  // Expose $bits so top can verify the type parameter resolved correctly
  assign req_bits_out = $bits(axi_req_t);
endmodule

//======================================================================
// axi_demux skeleton
//======================================================================
module axi_demux #(
  parameter int unsigned AxiIdWidth  = 32'd0,
  parameter type         aw_chan_t   = logic,
  parameter type         w_chan_t    = logic,
  parameter type         b_chan_t    = logic,
  parameter type         ar_chan_t   = logic,
  parameter type         r_chan_t    = logic,
  parameter type         axi_req_t  = logic,
  parameter type         axi_resp_t = logic,
  parameter int unsigned NoMstPorts  = 32'd0,
  parameter int unsigned MaxTrans    = 32'd8,
  parameter int unsigned AxiLookBits = 32'd3
)(
  input  logic     clk_i,
  input  logic     rst_ni,
  input  axi_req_t slv_req_i,
  output axi_resp_t slv_resp_o,
  output logic [AxiLookBits-1:0] id_out,
  output int unsigned req_bits_out
);
  axi_demux_simple #(
    .AxiIdWidth  ( AxiIdWidth  ),
    .axi_req_t   ( axi_req_t   ),
    .axi_resp_t  ( axi_resp_t  ),
    .AxiLookBits ( AxiLookBits )
  ) i_demux_simple (
    .clk_i,
    .rst_ni,
    .slv_req_i,
    .slv_resp_o,
    .id_out,
    .req_bits_out
  );
endmodule

//======================================================================
// axi_burst_splitter skeleton
//======================================================================
module axi_burst_splitter #(
  parameter int unsigned AddrWidth  = 32'd0,
  parameter int unsigned DataWidth  = 32'd0,
  parameter int unsigned IdWidth    = 32'd0,
  parameter int unsigned UserWidth  = 32'd0,
  parameter type         axi_req_t  = logic,
  parameter type         axi_resp_t = logic
)(
  input  logic     clk_i,
  input  logic     rst_ni,
  input  axi_req_t slv_req_i,
  output axi_resp_t slv_resp_o,
  output logic [IdWidth-1:0] id_out
);
  typedef logic [AddrWidth-1:0]   addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [UserWidth-1:0]   user_t;

  typedef struct packed {
    id_t   id;
    addr_t addr;
    logic [7:0] len;
    logic [2:0] size;
    logic [1:0] burst;
  } local_aw_chan_t;

  typedef struct packed { data_t data; strb_t strb; logic last; } local_w_chan_t;
  typedef struct packed { id_t id; logic [1:0] resp; } local_b_chan_t;
  typedef struct packed { id_t id; addr_t addr; logic [7:0] len; logic [2:0] size; logic [1:0] burst; } local_ar_chan_t;
  typedef struct packed { id_t id; data_t data; logic [1:0] resp; logic last; } local_r_chan_t;

  int unsigned req_bits_out;

  axi_demux #(
    .AxiIdWidth  ( IdWidth          ),
    .aw_chan_t   ( local_aw_chan_t  ),
    .w_chan_t    ( local_w_chan_t   ),
    .b_chan_t    ( local_b_chan_t   ),
    .ar_chan_t   ( local_ar_chan_t  ),
    .r_chan_t    ( local_r_chan_t   ),
    .axi_req_t   ( axi_req_t        ),
    .axi_resp_t  ( axi_resp_t       ),
    .NoMstPorts  ( 2                ),
    .MaxTrans    ( 4                ),
    .AxiLookBits ( IdWidth          )
  ) i_demux (
    .clk_i, .rst_ni,
    .slv_req_i, .slv_resp_o, .id_out,
    .req_bits_out
  );
endmodule

//======================================================================
// axi_dw_upsizer skeleton
//======================================================================
module axi_dw_upsizer #(
  parameter int unsigned AxiIdWidth          = 1,
  parameter int unsigned AxiAddrWidth        = 1,
  parameter type         aw_chan_t           = logic,
  parameter type         mst_w_chan_t        = logic,
  parameter type         slv_w_chan_t        = logic,
  parameter type         b_chan_t            = logic,
  parameter type         ar_chan_t           = logic,
  parameter type         mst_r_chan_t        = logic,
  parameter type         slv_r_chan_t        = logic,
  parameter type         axi_mst_req_t      = logic,
  parameter type         axi_mst_resp_t     = logic,
  parameter type         axi_slv_req_t      = logic,
  parameter type         axi_slv_resp_t     = logic
)(
  input  logic          clk_i,
  input  logic          rst_ni,
  input  axi_slv_req_t  slv_req_i,
  output axi_slv_resp_t slv_resp_o,
  output axi_mst_req_t  mst_req_o,
  input  axi_mst_resp_t mst_resp_i
);
  axi_mst_req_t  mst_req;
  axi_mst_resp_t mst_resp;
  logic [AxiIdWidth-1:0] id_out;
  int unsigned req_bits_out;

  assign mst_req = '0;
  assign slv_resp_o = '0;
  assign mst_req_o = mst_req;

  axi_demux #(
    .AxiIdWidth  ( AxiIdWidth       ),
    .aw_chan_t   ( aw_chan_t        ),
    .w_chan_t    ( mst_w_chan_t     ),
    .b_chan_t    ( b_chan_t         ),
    .ar_chan_t   ( ar_chan_t        ),
    .r_chan_t    ( mst_r_chan_t     ),
    .axi_req_t   ( axi_mst_req_t    ),
    .axi_resp_t  ( axi_mst_resp_t   ),
    .NoMstPorts  ( 2                ),
    .MaxTrans    ( 4                ),
    .AxiLookBits ( AxiIdWidth       )
  ) i_axi_demux (
    .clk_i, .rst_ni,
    .slv_req_i  ( mst_req  ),
    .slv_resp_o ( mst_resp ),
    .id_out,
    .req_bits_out
  );
endmodule

//======================================================================
// axi_dw_converter skeleton — generate if for upsize
//======================================================================
module axi_dw_converter #(
  parameter int unsigned AxiSlvPortDataWidth = 8,
  parameter int unsigned AxiMstPortDataWidth = 8,
  parameter int unsigned AxiAddrWidth        = 1,
  parameter int unsigned AxiIdWidth          = 1,
  parameter type         aw_chan_t           = logic,
  parameter type         mst_w_chan_t        = logic,
  parameter type         slv_w_chan_t        = logic,
  parameter type         b_chan_t            = logic,
  parameter type         ar_chan_t           = logic,
  parameter type         mst_r_chan_t        = logic,
  parameter type         slv_r_chan_t        = logic,
  parameter type         axi_mst_req_t      = logic,
  parameter type         axi_mst_resp_t     = logic,
  parameter type         axi_slv_req_t      = logic,
  parameter type         axi_slv_resp_t     = logic
)(
  input  logic          clk_i,
  input  logic          rst_ni,
  input  axi_slv_req_t  slv_req_i,
  output axi_slv_resp_t slv_resp_o,
  output axi_mst_req_t  mst_req_o,
  input  axi_mst_resp_t mst_resp_i
);
  if (AxiMstPortDataWidth == AxiSlvPortDataWidth) begin : gen_no_dw_conversion
    assign mst_req_o  = slv_req_i;
    assign slv_resp_o = mst_resp_i;
  end

  if (AxiMstPortDataWidth > AxiSlvPortDataWidth) begin : gen_dw_upsize
    axi_dw_upsizer #(
      .AxiAddrWidth        ( AxiAddrWidth        ),
      .AxiIdWidth          ( AxiIdWidth          ),
      .aw_chan_t           ( aw_chan_t           ),
      .mst_w_chan_t        ( mst_w_chan_t        ),
      .slv_w_chan_t        ( slv_w_chan_t        ),
      .b_chan_t            ( b_chan_t            ),
      .ar_chan_t           ( ar_chan_t           ),
      .mst_r_chan_t        ( mst_r_chan_t        ),
      .slv_r_chan_t        ( slv_r_chan_t        ),
      .axi_mst_req_t       ( axi_mst_req_t       ),
      .axi_mst_resp_t      ( axi_mst_resp_t      ),
      .axi_slv_req_t       ( axi_slv_req_t       ),
      .axi_slv_resp_t      ( axi_slv_resp_t      )
    ) i_axi_dw_upsizer (
      .clk_i, .rst_ni,
      .slv_req_i, .slv_resp_o,
      .mst_req_o, .mst_resp_i
    );
  end

  // Expose leaf req_bits from whichever generate path is active
  int unsigned mst_req_bits;
  if (AxiMstPortDataWidth > AxiSlvPortDataWidth) begin : gen_bits_up
    assign mst_req_bits = gen_dw_upsize.i_axi_dw_upsizer.req_bits_out;
  end else begin : gen_bits_eq
    assign mst_req_bits = 0;
  end
endmodule

//======================================================================
// axi_to_axi_lite skeleton
//======================================================================
module axi_to_axi_lite #(
  parameter int unsigned AxiAddrWidth = 32'd0,
  parameter int unsigned AxiDataWidth = 32'd0,
  parameter int unsigned AxiIdWidth   = 32'd0,
  parameter int unsigned AxiUserWidth = 32'd0,
  parameter type         full_req_t   = logic,
  parameter type         full_resp_t  = logic
)(
  input  logic      clk_i,
  input  logic      rst_ni,
  input  full_req_t slv_req_i,
  output full_resp_t slv_resp_o,
  output logic [AxiIdWidth-1:0] id_out
);
  axi_burst_splitter #(
    .AddrWidth  ( AxiAddrWidth ),
    .DataWidth  ( AxiDataWidth ),
    .IdWidth    ( AxiIdWidth   ),
    .UserWidth  ( AxiUserWidth ),
    .axi_req_t  ( full_req_t   ),
    .axi_resp_t ( full_resp_t  )
  ) i_axi_burst_splitter (
    .clk_i, .rst_ni,
    .slv_req_i, .slv_resp_o, .id_out
  );

  int unsigned req_bits_out;
  assign req_bits_out = i_axi_burst_splitter.req_bits_out;
endmodule

//======================================================================
// axi_to_axi_lite_wrap — non-parameterized wrapper (#()) with iface port
//======================================================================
module axi_to_axi_lite_wrap #()(
  input logic clk_i,
  input logic rst_ni,
  my_if.target axi_tgt_io
);
  typedef axi_tgt_io.req_t  tgt_req_t;
  typedef axi_tgt_io.resp_t tgt_resp_t;

  tgt_req_t tgt_req;
  tgt_resp_t tgt_resp;
  assign tgt_req = axi_tgt_io.req;
  assign axi_tgt_io.resp = tgt_resp;

  logic [axi_tgt_io.cfg.IdBits-1:0] id_result;
  int unsigned req_bits_out;

  axi_to_axi_lite #(
    .AxiAddrWidth ( 32                       ),
    .AxiDataWidth ( axi_tgt_io.cfg.DataBits  ),
    .AxiIdWidth   ( axi_tgt_io.cfg.IdBits    ),
    .AxiUserWidth ( 1                        ),
    .full_req_t   ( tgt_req_t                ),
    .full_resp_t  ( tgt_resp_t               )
  ) axi_to_axi_lite (
    .clk_i, .rst_ni,
    .slv_req_i  ( tgt_req  ),
    .slv_resp_o ( tgt_resp ),
    .id_out     ( id_result )
  );

  assign req_bits_out = axi_to_axi_lite.req_bits_out;
endmodule

//======================================================================
// axi_dw_converter_wrap — non-parameterized wrapper with TWO iface ports
//======================================================================
module axi_dw_converter_wrap #()(
  input logic clk_i,
  input logic rst_ni,
  my_if.target tgt_io,
  my_if.initiator mst_io
);
  typedef tgt_io.aw_chan_t  tgt_aw_chan_t;
  typedef tgt_io.w_chan_t   tgt_w_chan_t;
  typedef tgt_io.b_chan_t   tgt_b_chan_t;
  typedef tgt_io.ar_chan_t  tgt_ar_chan_t;
  typedef tgt_io.r_chan_t   tgt_r_chan_t;

  typedef mst_io.w_chan_t   mst_w_chan_t;
  typedef mst_io.r_chan_t   mst_r_chan_t;

  typedef tgt_io.req_t      tgt_req_t;
  typedef tgt_io.resp_t     tgt_resp_t;
  typedef mst_io.req_t      mst_req_t;
  typedef mst_io.resp_t     mst_resp_t;

  tgt_req_t tgt_req;
  tgt_resp_t tgt_resp;
  mst_req_t mst_req;
  mst_resp_t mst_resp;

  assign tgt_req = tgt_io.req;
  assign tgt_io.resp = tgt_resp;
  assign mst_io.req = mst_req;
  assign mst_resp = mst_io.resp;

  axi_dw_converter #(
    .AxiSlvPortDataWidth ( tgt_io.cfg.DataBits ),
    .AxiMstPortDataWidth ( mst_io.cfg.DataBits ),
    .AxiAddrWidth        ( 32                  ),
    .AxiIdWidth          ( tgt_io.cfg.IdBits   ),
    .aw_chan_t           ( tgt_aw_chan_t       ),
    .mst_w_chan_t        ( mst_w_chan_t        ),
    .slv_w_chan_t        ( tgt_w_chan_t        ),
    .b_chan_t            ( tgt_b_chan_t        ),
    .ar_chan_t           ( tgt_ar_chan_t       ),
    .mst_r_chan_t        ( mst_r_chan_t        ),
    .slv_r_chan_t        ( tgt_r_chan_t        ),
    .axi_mst_req_t       ( mst_req_t           ),
    .axi_mst_resp_t      ( mst_resp_t          ),
    .axi_slv_req_t       ( tgt_req_t           ),
    .axi_slv_resp_t      ( tgt_resp_t          )
  ) dw_converter (
    .clk_i, .rst_ni,
    .slv_req_i  ( tgt_req  ),
    .slv_resp_o ( tgt_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

  // Expose $bits from the mst-side leaf (through dw_converter -> upsizer -> demux)
  int unsigned mst_req_bits_out;
  assign mst_req_bits_out = dw_converter.mst_req_bits;

  // Also check tgt-side typedef width directly in this wrapper
  int unsigned tgt_req_bits_out;
  assign tgt_req_bits_out = $bits(tgt_req_t);
  int unsigned mst_req_bits_local;
  assign mst_req_bits_local = $bits(mst_req_t);
endmodule

//======================================================================
// Top module
//======================================================================
module t;
  logic clk;
  logic rst_n;

  // Config A: narrow ID (2 bits), narrow data (64 bits) -> upsize to 128
  localparam cfg_pkg::cfg_t CFG_A_SLV = '{IdBits: 2, DataBits: 64};
  localparam cfg_pkg::cfg_t CFG_A_MST = '{IdBits: 2, DataBits: 128};

  // Config B: wide ID (8 bits), data 64 bits
  localparam cfg_pkg::cfg_t CFG_B = '{IdBits: 8, DataBits: 64};

  my_if #(.cfg(CFG_A_SLV)) bus_a_slv();
  my_if #(.cfg(CFG_A_MST)) bus_a_mst();
  my_if #(.cfg(CFG_B))     bus_b();

  // Path A: dw_converter_wrap (narrow ID, upsize 64->128)
  axi_dw_converter_wrap #() u_dw_conv_wrap (
    .clk_i(clk), .rst_ni(rst_n),
    .tgt_io(bus_a_slv), .mst_io(bus_a_mst)
  );

  // Path B: axi_to_axi_lite_wrap (wide ID)
  axi_to_axi_lite_wrap #() u_axi_to_lite_wrap (
    .clk_i(clk), .rst_ni(rst_n),
    .axi_tgt_io(bus_b)
  );

  //======================================================================
  // Expected $bits values:
  //
  // req_t for CFG_A_SLV (Id=2, Data=64):
  //   aw_chan_t = 2+64+8+3+2 = 79
  //   w_chan_t  = 64+8+1 = 73
  //   ar_chan_t = 79
  //   req_t = 79+1+73+1+1+79+1+1 = 236
  //
  // req_t for CFG_A_MST (Id=2, Data=128):
  //   aw_chan_t = 2+128+8+3+2 = 143
  //   w_chan_t  = 128+16+1 = 145
  //   ar_chan_t = 143
  //   req_t = 143+1+145+1+1+143+1+1 = 436
  //
  // req_t for CFG_B (Id=8, Data=64):
  //   aw_chan_t = 8+64+8+3+2 = 85
  //   w_chan_t  = 64+8+1 = 73
  //   ar_chan_t = 85
  //   req_t = 85+1+73+1+1+85+1+1 = 248
  //======================================================================

  localparam int unsigned EXP_REQ_BITS_A_SLV = 236;
  localparam int unsigned EXP_REQ_BITS_A_MST = 436;
  localparam int unsigned EXP_REQ_BITS_B     = 248;

  // verilator lint_off STMTDLY
  initial begin
    clk = 0; rst_n = 1;

    // Drive path A: narrow ID
    bus_a_slv.req = '0;
    bus_a_slv.req.aw.id = 2'h3;
    bus_a_slv.req.aw_valid = 1'b1;
    bus_a_mst.resp = '0;

    // Drive path B: wide ID
    bus_b.req = '0;
    bus_b.req.aw.id = 8'hAB;
    bus_b.req.aw_valid = 1'b1;

    #10;

    //------------------------------------------------------------------
    // Check 1: dw_converter_wrap typedef widths
    // tgt_req_t must match CFG_A_SLV, mst_req_t must match CFG_A_MST
    //------------------------------------------------------------------
    if (u_dw_conv_wrap.tgt_req_bits_out !== EXP_REQ_BITS_A_SLV) begin
      $display("%%Error: dw_conv_wrap tgt_req_bits=%0d expected=%0d",
               u_dw_conv_wrap.tgt_req_bits_out, EXP_REQ_BITS_A_SLV);
      $stop;
    end
    if (u_dw_conv_wrap.mst_req_bits_local !== EXP_REQ_BITS_A_MST) begin
      $display("%%Error: dw_conv_wrap mst_req_bits_local=%0d expected=%0d",
               u_dw_conv_wrap.mst_req_bits_local, EXP_REQ_BITS_A_MST);
      $stop;
    end

    //------------------------------------------------------------------
    // Check 2: mst-side leaf (through dw_upsizer -> axi_demux -> axi_demux_simple)
    // axi_req_t must be mst_req_t = CFG_A_MST
    //------------------------------------------------------------------
    if (u_dw_conv_wrap.mst_req_bits_out !== EXP_REQ_BITS_A_MST) begin
      $display("%%Error: dw_conv_wrap mst leaf req_bits=%0d expected=%0d",
               u_dw_conv_wrap.mst_req_bits_out, EXP_REQ_BITS_A_MST);
      $stop;
    end

    //------------------------------------------------------------------
    // Check 3: axi_to_axi_lite_wrap leaf
    // axi_req_t must be tgt_req_t = CFG_B
    //------------------------------------------------------------------
    if (u_axi_to_lite_wrap.req_bits_out !== EXP_REQ_BITS_B) begin
      $display("%%Error: axi_to_lite leaf req_bits=%0d expected=%0d",
               u_axi_to_lite_wrap.req_bits_out, EXP_REQ_BITS_B);
      $stop;
    end

    //------------------------------------------------------------------
    // Check 4: ID extraction through path B
    // axi_to_axi_lite_wrap -> ... -> axi_demux_simple extracts aw.id[0+:8]
    //------------------------------------------------------------------
    if (u_axi_to_lite_wrap.id_result !== 8'hAB) begin
      $display("%%Error: axi_to_lite id_result=%0h expected=AB",
               u_axi_to_lite_wrap.id_result);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
  // verilator lint_on STMTDLY
endmodule
