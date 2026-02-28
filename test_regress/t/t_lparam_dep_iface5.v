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

package scp;
  typedef struct packed {
    int unsigned Associativity;
    int unsigned Capacity;
    int unsigned LineSize;
    int unsigned AddrBits;
  } cfg_t;
endpackage

interface sct_if #(
  parameter scp::cfg_t cfg = 0
)();

  // this is intentional as I want all the dependencies to be resolved
  localparam int  SC_NUM_LINES = cfg.Capacity / cfg.LineSize;
  localparam int  SC_LINES_PER_WAY = SC_NUM_LINES / cfg.Associativity;
  localparam int  SC_BLOCK_BITS = $clog2(cfg.LineSize);
  localparam int  SC_ROW_BITS = $clog2(SC_LINES_PER_WAY);
  localparam int  SC_TAG_BITS = cfg.AddrBits - SC_ROW_BITS - SC_BLOCK_BITS;

  typedef logic [SC_TAG_BITS-1:0] tag_t;
endinterface

interface sc_if #(
  parameter scp::cfg_t cfg = 0
)();
  sct_if #(cfg) types();
endinterface

module sc #(parameter scp::cfg_t cfg=0) (
  sc_if io
);
  sct_if #(cfg) types();

  typedef io.types.tag_t tag_t;
  typedef types.tag_t tag2_t;

  initial begin
    #1;
    `checkd(55, $bits(tag_t));
    `checkd(55, $bits(tag2_t));
  end
endmodule

module t();
  localparam scp::cfg_t sc_cfg = '{
    Associativity : 2,
    Capacity : 1024,
    LineSize : 64,
    AddrBits : 64
  };

  sc_if #(sc_cfg) sc_io ();

  typedef sc_io.types.tag_t tag_t;

  sc #(sc_cfg) sc(
    .io(sc_io)
  );

  initial begin
    #2;
    `checkd(55, $bits(tag_t));
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
