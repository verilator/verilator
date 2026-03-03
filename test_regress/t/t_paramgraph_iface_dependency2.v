// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package a_pkg;
  typedef struct packed {
    int unsigned a;
  } cfg_t;
endpackage

package b_pkg;
  typedef struct packed {
    int unsigned a;
  } cfg_t;
endpackage

interface depgraph_if #(a_pkg::cfg_t cfg=0)();
  typedef logic [cfg.a-1:0] byte_t;
  typedef logic [cfg.a*2-1:0] half_t;
  typedef struct packed {
    byte_t a;
    half_t b;
  } pair_t;
  typedef union packed {
    pair_t p;
    logic [23:0] flat;
  } pair_u_t;
endinterface

module t();
  localparam a_pkg::cfg_t cfg = '{
    a: 8
  };

  depgraph_if #(cfg) ifc();

  typedef ifc.pair_u_t pair_u_t;

  localparam b_pkg::cfg_t cfg_b = '{
    a:$bits(pair_u_t)
  };

  initial begin
    #2;
    `checkd(cfg_b.a, 24);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
