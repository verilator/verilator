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

interface depgraph_if #(a_pkg::cfg_t cfg=0)();
  typedef logic [cfg.a-1:0] byte_t;
  typedef struct packed {
      byte_t a;
  } pair_t;
endinterface

module a_mod(
  depgraph_if ifc
);
  typedef ifc.pair_t pair_t;

  localparam p_a = $bits(pair_t);

  initial begin
    #1;
    `checkd($bits(pair_t),8);
    `checkd(p_a, 8);
  end
endmodule

module t();
  localparam a_pkg::cfg_t cfg = '{
    a: 8
  };

  depgraph_if #(cfg) ifc();
  a_mod #() a_mod_0(
    .ifc(ifc)
  );

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
