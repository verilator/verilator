// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// DESCRIPTION:
// Regression for localparam-derived cfg structs feeding interface instances
// and their nested typedefs.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package cache_pkg;
  typedef struct packed {
    int Capacity;
    int LineSize;
    int Associativity;
    int AddrBits;
    int FgWidth;
    int MissQSize;
    int CmdTagBits;
  } cfg_t;
endpackage

interface cache_types_if #(
  parameter cache_pkg::cfg_t cfg = '0
)();
  localparam int SC_NUM_LINES = cfg.Capacity / cfg.LineSize;
  localparam int SC_LINES_PER_WAY = SC_NUM_LINES / cfg.Associativity;
  localparam int SC_BLOCK_BITS = $clog2(cfg.LineSize);
  localparam int SC_ROW_BITS = $clog2(SC_LINES_PER_WAY);
  localparam int SC_TAG_BITS = cfg.AddrBits - SC_ROW_BITS - SC_BLOCK_BITS;
  localparam int SC_NUM_DROWS = (cfg.LineSize / cfg.FgWidth) * SC_NUM_LINES;

  typedef logic [SC_TAG_BITS-1:0] tag_t;
  typedef logic [$clog2(SC_NUM_DROWS)-1:0] drow_addr_t;
endinterface

interface cache_if #(
  parameter cache_pkg::cfg_t cfg = '0
)();
  cache_types_if #(cfg) types();
  typedef types.tag_t tag_t;
  typedef types.drow_addr_t drow_addr_t;
endinterface

module cache_leaf(cache_if io, output int tag_bits_o, output int drow_bits_o);
  typedef io.tag_t tag_t;
  typedef io.drow_addr_t drow_addr_t;
  assign tag_bits_o = $bits(tag_t);
  assign drow_bits_o = $bits(drow_addr_t);
endmodule

module cache_wrap #(
  parameter cache_pkg::cfg_t cfg = '0
)(output int tag_bits_o, output int drow_bits_o);
  localparam cache_pkg::cfg_t sc_cfg = '{
    CmdTagBits : $clog2(cfg.Capacity),
    Associativity : cfg.Associativity,
    Capacity : cfg.Capacity,
    LineSize : cfg.LineSize,
    AddrBits : cfg.AddrBits,
    FgWidth : cfg.FgWidth,
    MissQSize : cfg.MissQSize
  };

  cache_if #(sc_cfg) sc_io();

  cache_leaf u_leaf(.io(sc_io), .tag_bits_o(tag_bits_o), .drow_bits_o(drow_bits_o));
endmodule

module top;
  localparam cache_pkg::cfg_t cfg0 = '{
    Capacity:1024, LineSize:64, Associativity:4, AddrBits:32,
    FgWidth:32, MissQSize:8, CmdTagBits:0
  };
  localparam cache_pkg::cfg_t cfg1 = '{
    Capacity:2048, LineSize:32, Associativity:2, AddrBits:36,
    FgWidth:16, MissQSize:16, CmdTagBits:0
  };

  int tag_bits0;
  int drow_bits0;
  int tag_bits1;
  int drow_bits1;

  cache_wrap #(cfg0) wrap0(.tag_bits_o(tag_bits0), .drow_bits_o(drow_bits0));
  cache_wrap #(cfg1) wrap1(.tag_bits_o(tag_bits1), .drow_bits_o(drow_bits1));

  initial begin
    #1;
    `checkd(tag_bits0, 24);
    `checkd(drow_bits0, 5);
    `checkd(tag_bits1, 26);
    `checkd(drow_bits1, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
