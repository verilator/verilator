// DESCRIPTION: Verilator: Test for structural disambiguation and wrong-clone
// fixup in V3LinkDotIfaceCapture.
//
// Modeled after Aerial's simple_cache_if pattern:
//   - A parameterized interface (sc_if) contains a nested sub-interface (sc_io)
//   - The sub-interface has typedefs (addr_t)
//   - A wrapper module (sc_wrap) instantiates sc_if and uses its typedefs
//   - Two different parameterizations of sc_wrap exist
//   - The re-exported typedefs from sc_io create entries where followCellPath
//     may fail, triggering the structural disambiguation path
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

typedef struct packed {
    int unsigned AddrBits;
    int unsigned DataBits;
} sc_cfg_t;

// Inner types interface - parameterized with struct typedef
interface sc_types_if #(parameter sc_cfg_t cfg = 0)();
    typedef logic [cfg.AddrBits-1:0] addr_t;
    typedef logic [cfg.DataBits-1:0] data_t;

    typedef struct packed {
        addr_t addr;
        data_t data;
    } pkt_t;
endinterface

// Cache interface - wraps types interface and re-exports typedefs
interface sc_if #(parameter sc_cfg_t cfg = 0)();
    sc_types_if #(cfg) sc_io();

    typedef sc_io.addr_t addr_t;
    typedef sc_io.data_t data_t;
    typedef sc_io.pkt_t  pkt_t;

    addr_t rq_addr_i;
endinterface

// Wrapper module that uses the cache interface
// The consumer references the sc_io sub-interface's typedefs
module sc_wrap #(parameter sc_cfg_t cfg = 0)();
    sc_if #(cfg) cache();

    typedef cache.addr_t addr_t;
    typedef cache.pkt_t  pkt_t;

    addr_t local_addr;
    pkt_t  local_pkt;

    assign cache.rq_addr_i = local_addr;
endmodule

// Top-level: two wrappers with DIFFERENT configs
// This creates two clones of sc_if (and sc_types_if) with different params
module t;
    localparam sc_cfg_t cfg_narrow = '{AddrBits: 16, DataBits: 32};
    localparam sc_cfg_t cfg_wide   = '{AddrBits: 32, DataBits: 64};

    sc_wrap #(.cfg(cfg_narrow)) narrow();
    sc_wrap #(.cfg(cfg_wide))   wide();

    initial begin
        #1;
        // narrow: addr=16, data=32, pkt=16+32=48
        `checkd($bits(narrow.local_addr), 16);
        `checkd($bits(narrow.local_pkt), 48);

        // wide: addr=32, data=64, pkt=32+64=96
        `checkd($bits(wide.local_addr), 32);
        `checkd($bits(wide.local_pkt), 96);

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
