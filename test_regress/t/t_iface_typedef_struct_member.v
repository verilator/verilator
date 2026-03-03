// DESCRIPTION: Verilator: Test for MemberDType fixup and fixDeadRefs in type table (coverage)
//
// Parameterized interface with struct/union typedefs, instantiated in two
// modules.  The sub-module uses $bits() on a typedef, which forces widthing
// of the template's type chain during V3Param.  This moves template RefDTypes
// into the global type table before the template dies, exercising
// fixDeadRefsInTypeTable and the MemberDType fixup in V3LinkDotIfaceCapture.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package cfg_pkg;
  typedef struct packed {
    int unsigned NumUnits;
    int unsigned LineSize;
  } cfg_t;
endpackage

// Parameterized interface with nested struct/union typedefs.
// The struct-in-union pattern triggers MemberDType fixup (line 1056).
// The $bits() usage in sub_mod forces widthing during V3Param, moving
// template RefDTypes into the type table before the template dies.
interface types_if #(parameter cfg_pkg::cfg_t cfg = 0)();
  typedef logic [$clog2(cfg.NumUnits)-1:0] idx_t;

  typedef struct packed {
    logic [31:$clog2(cfg.LineSize)] tag;
    logic [$clog2(cfg.LineSize)-1:0] offset;
  } addr_t;

  typedef struct packed {
    logic [3:0] cmd;
    union packed {
      addr_t       addr;   // struct-in-union: MemberDType trigger
      logic [31:0] raw;
    } payload;
  } req_t;
endinterface

module sub_mod #(parameter cfg_pkg::cfg_t cfg = 0)();
  types_if #(cfg) types();
  typedef types.idx_t  idx_t;
  typedef types.req_t  req_t;
  typedef types.addr_t addr_t;

  localparam int ReqWidth = $bits(req_t);

  idx_t  s_idx;
  req_t  s_req;
  addr_t s_addr;
endmodule

module t;
  localparam cfg_pkg::cfg_t CFG = '{NumUnits: 5, LineSize: 32};

  types_if #(CFG) types();
  typedef types.req_t req_t;
  req_t top_req;

  sub_mod #(.cfg(CFG)) sub();

  initial begin
    #1;
    `checkd($bits(top_req), 36);
    `checkd($bits(sub.s_req), 36);
    `checkd($bits(sub.s_idx), 3);
    `checkd($bits(sub.s_addr), 32);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
