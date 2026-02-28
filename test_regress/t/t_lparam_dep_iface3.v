// DESCRIPTION: Verilator: Get agregate type parameter from array of interfaces
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package sc;
  typedef struct packed {
    int unsigned CmdTagBits;
    int unsigned Associativity;
    int unsigned Capacity;
    int unsigned LineSize;
    int unsigned StateBits;
    int unsigned AddrBits;
    int unsigned MissQSize;

    // fetch (hit) width.  this must be >= to refill width.  FgWidth / RefillWidth is the number of array slices for data.
    int unsigned FgWidth;
    // number of expected beats for refill is LineSize/RefillWidth
    int unsigned RefillWidth;
  } cfg_t;
endpackage

interface simple_cache_types_if #(
  parameter sc::cfg_t cfg = 0
)();

  localparam int  SC_NUM_LINES = cfg.Capacity / cfg.LineSize;
  localparam int  SC_LINES_PER_WAY = SC_NUM_LINES / cfg.Associativity;
  localparam int  SC_BLOCK_BITS = $clog2(cfg.LineSize);
  localparam int  SC_ROW_BITS = $clog2(SC_LINES_PER_WAY);
  localparam int  SC_TAG_BITS = cfg.AddrBits - SC_ROW_BITS - SC_BLOCK_BITS;
  localparam int  SC_DROWS_PER_LINE = cfg.LineSize / cfg.FgWidth;
  localparam int  SC_NUM_DROWS = SC_NUM_LINES * SC_DROWS_PER_LINE;

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

  typedef struct packed {
    logic vld;
    tag_t tag;
    state_t state;
  } sc_tag_t;

  typedef struct packed {
    state_t [cfg.Associativity-1:0] state_v;
    assoc_oh_t hit_v;
    assoc_oh_t vld_v;
    plru_t plru;
  } sc_tag_status_t;
endinterface

interface simple_cache_if #(
  parameter sc::cfg_t cfg = 0
)();
  simple_cache_types_if #(cfg) types();

  typedef types.cmd_tag_t cmd_tag_t;
  typedef types.addr_t addr_t;
  typedef types.missq_tag_t missq_tag_t;

endinterface

module simple_cache #(parameter sc::cfg_t cfg=0) (
  simple_cache_if io
);

  typedef io.types.addr_t addr_t;
  typedef io.types.cmd_tag_t cmd_tag_t;
  typedef io.types.drow_addr_t drow_addr_t;
  typedef io.types.plru_t plru_t;
  typedef io.types.row_t row_t;
  typedef io.types.state_t state_t;
  typedef io.types.sc_tag_addr_t sc_tag_addr_t;
  typedef io.types.sc_tag_t sc_tag_t;
  typedef io.types.sc_tag_status_t sc_tag_status_t;

  localparam num_rld_beats = cfg.LineSize / cfg.RefillWidth;
  localparam num_arrays = cfg.FgWidth / cfg.RefillWidth;
  localparam dat_array_width = cfg.RefillWidth*8;
  localparam int  SC_DROWS_PER_LINE = io.types.SC_DROWS_PER_LINE;
  localparam int  SC_NUM_LINES = io.types.SC_NUM_LINES;
  localparam int  SC_LINES_PER_WAY = io.types.SC_LINES_PER_WAY;
  localparam int  SC_NUM_DROWS = io.types.SC_NUM_DROWS;

  initial begin
    #1;
    `checkd(SC_DROWS_PER_LINE, 4);
    `checkd(SC_NUM_LINES, 16);
    `checkd(SC_LINES_PER_WAY, 8);
    `checkd(SC_NUM_DROWS, 64);
    `checkd(num_rld_beats, 8);
    `checkd(num_arrays, 2);
    `checkd(dat_array_width, 64);
  end

endmodule


module t();

  localparam sc::cfg_t sc_cfg = '{
    CmdTagBits : $clog2(6),
    Associativity : 2,
    Capacity : 1024,
    LineSize : 64,
    StateBits : 2,
    AddrBits : 64,
    MissQSize : 2,

    FgWidth : 16,
    RefillWidth : 8
  };

  simple_cache_if #(sc_cfg) sc_io ();

  simple_cache #(sc_cfg) simple_cache(
    .io(sc_io)
  );

  //localparam int  SC_DROWS_PER_LINE = sc_io.types.SC_DROWS_PER_LINE;
  //localparam int  SC_NUM_LINES = sc_io.types.SC_NUM_LINES;
  //localparam int  SC_LINES_PER_WAY = sc_io.types.SC_LINES_PER_WAY;
  //localparam int  SC_NUM_DROWS = sc_io.types.SC_NUM_DROWS;

  initial begin
    #2;
    //`checkd(SC_DROWS_PER_LINE, 4);
    //`checkd(SC_NUM_LINES, 16);
    //`checkd(SC_LINES_PER_WAY, 8);
    //`checkd(SC_NUM_DROWS, 64);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
