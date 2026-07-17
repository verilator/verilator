// DESCRIPTION: Verilator: interface typedef $bits() capture use-after-free
//
// V3Width's $bits fold deletes a captured AstRefDType during V3Param::param
// (ParamVisitor::visit(AstVar*) -> constifyParamsEdit -> widthParamsEdit ->
// WidthVisitor::visit(AstAttrOf*)). A mid-pass consumer then walks the freed
// node: ParamProcessor::deepCloneModule -> forEach -> findOwnerModule.
//
// This is a pure use-after-free: the $bits fold computes the correct constant
// before freeing, so no value is wrong. It therefore fails under
// --enable-dev-asan (heap-use-after-free), and -- once the findOwnerModule
// address guard is removed -- as a deterministic SIGSEGV in a --debug build.
//
// Needs all four of: a parameterized interface whose typedef depends on the
// parameter; $bits() of the DOTTED ref directly, in param context; a
// STRUCT-typed parameter; and two differently-parameterized instances (to
// force V3Param to clone).
//
// NOTE: no comment line may begin with the word after the slashes that names
// the tool -- it is parsed as a metacomment pragma (BADVLTPRAGMA).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {int unsigned W;} cfg_t;

interface types_if #(parameter cfg_t cfg = '{default: 0});
   typedef logic [cfg.W-1:0] rq_t;
endinterface

module body #(parameter cfg_t cfg = '{default: 0});
   types_if #(cfg) types();
   localparam int DW = $bits(types.rq_t);  // AstAttrOf(DIM_BITS) over captured ref
   logic [DW-1:0] v;
   initial v = '0;
endmodule

module t;
   body #('{W: 8})  b0();
   body #('{W: 16}) b1();
endmodule
