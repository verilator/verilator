// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// DESCRIPTION: Verilator: TRULY BLENDED test for interface typedef resolution
// This test BLENDS both patterns into a single interacting structure:
// - Sibling cells (like t_lparam_dep_iface10)
// - Nested interface chains (like aerial_wrap)
// - COMBINED: Sibling cells that EACH contain nested interface chains
//
// The key test: A module accesses typedefs from TWO sibling nested interface
// chains, and each must resolve to the correct parameterized type.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

typedef struct packed {
  int unsigned AddrBits;
  int unsigned DataBits;
  int unsigned IdBits;
} axi_cfg_t;

// INNERMOST: Parameterized interface with typedefs
interface axi4_if #(parameter axi_cfg_t cfg = 0)();
  localparam int unsigned AddrBits = cfg.AddrBits * 2;
  localparam int unsigned DataBits = cfg.DataBits * 2;
  localparam int unsigned IdBits = cfg.IdBits * 2;

  typedef logic [AddrBits-1:0] addr_t;
  typedef logic [DataBits-1:0] data_t;
  typedef logic [IdBits-1:0] id_t;

  typedef struct packed {
    id_t     id;
    addr_t   addr;
  } ar_chan_t;

  typedef struct packed {
    id_t     id;
    data_t   data;
  } r_chan_t;

  ar_chan_t ar;
  r_chan_t  r;
endinterface

// MIDDLE: Interface that wraps axi4_if and re-exports its typedefs
interface tlb_io_if #(parameter axi_cfg_t axi_cfg = 0)();
  axi4_if #(.cfg(axi_cfg)) axi_tlb_io();

  // Re-export typedefs from nested interface
  typedef axi_tlb_io.r_chan_t r_chan_t;
  typedef axi_tlb_io.ar_chan_t ar_chan_t;
endinterface

// OUTER: Interface with TWO SIBLING tlb_io_if instances with DIFFERENT params
// This is the BLENDED pattern: sibling cells + nested chains
interface cca_io_if #(
  parameter axi_cfg_t axi_cfg_a = 0,
  parameter axi_cfg_t axi_cfg_b = 0
)();
  // SIBLING CELLS - same interface type, DIFFERENT params
  tlb_io_if #(.axi_cfg(axi_cfg_a)) tlb_io_a();
  tlb_io_if #(.axi_cfg(axi_cfg_b)) tlb_io_b();

  // Re-export from each sibling (these should be DIFFERENT types)
  typedef tlb_io_a.r_chan_t r_chan_a_t;
  typedef tlb_io_b.r_chan_t r_chan_b_t;
endinterface

// MODULE: Accesses typedefs from BOTH sibling nested chains via interface port
// This is the CRITICAL test - must distinguish between tlb_io_a and tlb_io_b
module cca_xbar (
  cca_io_if cca_io
);
  // Access typedefs through SIBLING nested interface chains
  // These MUST resolve to DIFFERENT types based on the different params
  typedef cca_io.tlb_io_a.r_chan_t m_r_chan_a_t;  // From axi_cfg_a
  typedef cca_io.tlb_io_b.r_chan_t m_r_chan_b_t;  // From axi_cfg_b
  typedef cca_io.tlb_io_a.ar_chan_t m_ar_chan_a_t;
  typedef cca_io.tlb_io_b.ar_chan_t m_ar_chan_b_t;

  m_r_chan_a_t r_data_a;
  m_r_chan_b_t r_data_b;

  initial begin
    #1;
    // axi_cfg_a: AddrBits=32, DataBits=64, IdBits=4
    // r_chan_t = id(4) + data(64)  = 68 bits * 2 = 136 bits
    // ar_chan_t = id(4) + addr(32)  = 36 bits * 2 = 72 bits
    `checkd($bits(m_r_chan_a_t), 136);
    `checkd($bits(m_ar_chan_a_t), 72);

    // axi_cfg_b: AddrBits=40, DataBits=128, IdBits=8
    // r_chan_t = id(8) + data(128)  = 136 bits * 2 = 272 bits
    // ar_chan_t = id(8) + addr(40)  = 48 bits * 2 = 96 bits
    `checkd($bits(m_r_chan_b_t), 272);
    `checkd($bits(m_ar_chan_b_t), 96);
  end
endmodule

// TOP MODULE
module t();
  localparam axi_cfg_t cfg_a = '{AddrBits: 32, DataBits: 64, IdBits: 4};
  localparam axi_cfg_t cfg_b = '{AddrBits: 40, DataBits: 128, IdBits: 8};

  cca_io_if #(.axi_cfg_a(cfg_a), .axi_cfg_b(cfg_b)) cca_io();
  cca_xbar xbar(.cca_io(cca_io));

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
