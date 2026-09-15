// DESCRIPTION: Verilator: Verilog Test module
//
// `outer_pkg::Alias::member`, where `Alias` is a typedef in `outer_pkg` that
// aliases a parameterized class from another package.
//
// Until the class is specialized in V3Param the alias's RHS is still a
// RefDType carrying its own scope, so classOrPackageSkipp() walks to null.
// Code that tested only Skipp therefore treated the (already resolved) ref as
// unresolved and re-looked-up its bare name in the referencing module's scope,
// where `Alias` is not visible - reporting "Package/class for ':: reference'
// not found".  Resolving from a submodule is what exposes it; with the
// referencing module as top the enclosing scope happens to still find it.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package base_pkg;
  typedef struct packed {
    int depth;
    int meta;
  } config_t;

  virtual class cfg #(
      parameter config_t c
  );
    localparam int width = $clog2(c.depth);
    typedef logic [width-1:0] data_t;
    typedef struct packed {
      logic [c.meta-1:0] m;
      data_t             d;
    } meta_t;
  endclass
endpackage

package top_pkg;
  localparam base_pkg::config_t cfgv = '{depth: 512, meta: 4};
  // Typedef alias of a parameterized class, in a different package
  typedef base_pkg::cfg #(cfgv) AliasCFG;
endpackage

// Alias-scoped type as a port, and in the body, of an instantiated submodule
module Leaf (
    input  top_pkg::AliasCFG::meta_t   in_meta,
    output top_pkg::AliasCFG::data_t   out_data
);
  top_pkg::AliasCFG::meta_t body_meta;
  always_comb begin
    body_meta = in_meta;
    out_data  = body_meta.d;
  end
  initial begin
    `checkh($bits(in_meta), 13);
    `checkh($bits(out_data), 9);
  end
endmodule

module Mid ();
  top_pkg::AliasCFG::meta_t m;
  top_pkg::AliasCFG::data_t d;
  Leaf leaf (
      .in_meta  (m),
      .out_data (d)
  );
  initial m = '0;
endmodule

module t;
  Mid mid ();
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
