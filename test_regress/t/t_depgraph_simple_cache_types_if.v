// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// DESCRIPTION:
// Minimal testcase for depgraph handling of localparam-derived typedefs
// inside a parameterized cache types interface.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package sc_pkg;
  typedef struct packed {
    int Capacity;
    int LineSize;
    int Associativity;
    int AddrBits;
    int FgWidth;
    int StateBits;
    int CmdTagBits;
    int MissQSize;
  } cfg_t;
endpackage

interface simple_cache_types_if #(
  parameter sc_pkg::cfg_t cfg = '0
)();
  localparam int SC_NUM_LINES = cfg.Capacity / cfg.LineSize;
  localparam int SC_LINES_PER_WAY = SC_NUM_LINES / cfg.Associativity;
  localparam int SC_BLOCK_BITS = $clog2(cfg.LineSize);
  localparam int SC_ROW_BITS = $clog2(SC_LINES_PER_WAY);
  localparam int SC_TAG_BITS = cfg.AddrBits - SC_ROW_BITS - SC_BLOCK_BITS;
  localparam int SC_DROWS_PER_LINE = cfg.LineSize / cfg.FgWidth;
  localparam int SC_NUM_DROWS = SC_NUM_LINES * SC_DROWS_PER_LINE;

  typedef logic [cfg.AddrBits-1:0] addr_t;
  typedef logic [cfg.Associativity-1:0] assoc_oh_t;
  typedef logic [cfg.Associativity-2:0] plru_t;
  typedef logic [cfg.StateBits-1:0] state_t;
  typedef logic [cfg.CmdTagBits-1:0] cmd_tag_t;
  typedef logic [$clog2(cfg.MissQSize)-1:0] missq_tag_t;

  typedef logic [SC_TAG_BITS-1:0] tag_t;
  typedef logic [SC_ROW_BITS-1:0] row_t;
  typedef logic [SC_BLOCK_BITS-1:0] block_t;
  typedef logic [$clog2(SC_NUM_DROWS)-1:0] drow_addr_t;

  typedef struct packed {
    tag_t tag;
    row_t row;
    block_t block;
  } sc_tag_addr_t;
endinterface

module child(simple_cache_types_if types, output int tag_bits_o,
             output int tag_addr_bits_o, output int drow_bits_o);
  typedef types.tag_t tag_t;
  typedef types.sc_tag_addr_t sc_tag_addr_t;
  typedef types.drow_addr_t drow_addr_t;
  assign tag_bits_o = $bits(tag_t);
  assign tag_addr_bits_o = $bits(sc_tag_addr_t);
  assign drow_bits_o = $bits(drow_addr_t);
endmodule

module top;
  localparam sc_pkg::cfg_t cfg0 = '{
    Capacity:1024, LineSize:64, Associativity:4, AddrBits:32,
    FgWidth:32, StateBits:2, CmdTagBits:5, MissQSize:8
  };
  localparam sc_pkg::cfg_t cfg1 = '{
    Capacity:2048, LineSize:32, Associativity:2, AddrBits:36,
    FgWidth:16, StateBits:3, CmdTagBits:7, MissQSize:16
  };

  simple_cache_types_if #(cfg0) types0();
  simple_cache_types_if #(cfg1) types1();

  int tag_bits0;
  int tag_addr_bits0;
  int drow_bits0;
  int tag_bits1;
  int tag_addr_bits1;
  int drow_bits1;

  child u0(.types(types0), .tag_bits_o(tag_bits0), .tag_addr_bits_o(tag_addr_bits0),
           .drow_bits_o(drow_bits0));
  child u1(.types(types1), .tag_bits_o(tag_bits1), .tag_addr_bits_o(tag_addr_bits1),
           .drow_bits_o(drow_bits1));

  initial begin
    #1;
    `checkd(tag_bits0, 24);
    `checkd(tag_addr_bits0, 32);
    `checkd(drow_bits0, 5);
    `checkd(tag_bits1, 26);
    `checkd(tag_addr_bits1, 36);
    `checkd(drow_bits1, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
