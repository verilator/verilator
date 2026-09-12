// DESCRIPTION: Verilator: Verilog Test module
//
// A middle segment of a `::` chain that aliases a parameterized class which is
// not yet specialized has no reachable module to resolve the following segment
// in.  This is legal SystemVerilog that Verilator does not yet support, so it
// must report gracefully rather than hit an internal assertion.
//
// Kept separate from t_class_scope_chain_bad.v because the errors there abort
// the pass before a later declaration would be reached.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package P;
  typedef struct packed {
    int depth;
  } config_t;

  virtual class PC #(
      parameter config_t c
  );
    localparam int width = $clog2(c.depth);
    virtual class inner;
      typedef logic [width-1:0] u;
    endclass
  endclass
endpackage

package Q;
  localparam P::config_t cfgv = '{depth: 16};
  typedef P::PC#(cfgv) AliasPC;
endpackage

// Referencing from an instantiated submodule is what leaves the alias
// unspecialized at the time the chain is resolved.
module Leaf ();
  Q::AliasPC::inner::u e;
  initial if ($bits(e) != 4) $stop;
endmodule

module t;
  Leaf leaf ();
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
