// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
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
endinterface

module a_mod(
  depgraph_if ifc
);
  typedef ifc.pair_t pair_t;
  typedef ifc.half_t half_t;

  localparam p_a = $bits(pair_t);
  localparam p_b = $bits(half_t);

  initial begin
    #1;
    `checkd($bits(pair_t),24);
    `checkd(p_a, 24);
    `checkd(p_b, 16);
  end
endmodule

module t();
  localparam a_pkg::cfg_t cfg = '{
    a: 8
  };

  depgraph_if #(cfg) ifc();

  typedef ifc.byte_t byte_t;

  a_mod #() a_mod_0(
    .ifc(ifc)
  );

  localparam b_pkg::cfg_t cfg_b = '{
    a:$bits(byte_t)
  };

  initial begin
    #2;
    `checkd(cfg_b.a, 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
