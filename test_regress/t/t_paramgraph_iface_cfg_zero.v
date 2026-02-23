// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// DESCRIPTION:
// Minimal testcase for depgraph interface typedef resolution
// Derived from aicc_types_if/axis_if ASCRANGE warnings
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package aerial;
  typedef struct packed {
    int NumCc;
    int CCNumWaves;
    int CCNumIds;
  } cfg_t;
endpackage

interface aicc_types_if #(parameter aerial::cfg_t cfg = '0)();
  typedef logic [$clog2(cfg.NumCc)-1:0] cc_index_t;
  typedef logic [$clog2(cfg.CCNumIds)-1:0] trans_id_t;
endinterface

module child(aicc_types_if types);
  localparam type cc_index_t = types.cc_index_t;
  localparam type trans_id_t = types.trans_id_t;
  cc_index_t cc_idx;
  trans_id_t tr_id;
endmodule

module top;
  localparam aerial::cfg_t aer_cfg = '{NumCc:4, CCNumWaves:2, CCNumIds:8};
  aicc_types_if #(.cfg(aer_cfg)) types();
  child u_child(.types(types));

  initial begin
    #2;
    `checkd($bits(types.cc_index_t), 2);
    `checkd($bits(types.trans_id_t), 3);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
