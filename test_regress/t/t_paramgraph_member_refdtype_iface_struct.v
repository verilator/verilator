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

interface depgraph_if;
  typedef logic [7:0] byte_t;
  typedef struct packed {
    byte_t a;
    byte_t b;
  } pair_t;
endinterface

module t_paramgraph_member_refdtype_iface_struct;
  depgraph_if ifc();

  typedef ifc.byte_t byte_t;
  typedef ifc.pair_t pair_t;

  pair_t p;
  logic [15:0] flat;

  assign flat = {p.a, p.b};

  initial begin
    #1;
    `checkd($bits(byte_t), 8);
    `checkd($bits(pair_t), 16);
    `checkd($bits(flat), 16);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
