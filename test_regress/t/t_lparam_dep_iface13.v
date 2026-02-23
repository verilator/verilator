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

endinterface

interface simple_cache_if #(
  parameter sc::cfg_t cfg = 0
)();
  simple_cache_types_if #(cfg) types();

endinterface

module simple_cache #(parameter sc::cfg_t cfg=0) (
  simple_cache_if io
);

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
    CmdTagBits : $clog2(6)
    ,Associativity : 2
    ,Capacity : 1024
    ,LineSize : 64
    ,StateBits : 2
    ,AddrBits : 64
    ,MissQSize : 2

    ,FgWidth : 16
    ,RefillWidth : 8
  };

  simple_cache_if #(sc_cfg) sc_io ();

  simple_cache #(sc_cfg) simple_cache(
    .io(sc_io)
  );

  localparam int  SC_DROWS_PER_LINE = sc_io.types.SC_DROWS_PER_LINE;

  initial begin
    #2;
    `checkd(SC_DROWS_PER_LINE, 4);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
