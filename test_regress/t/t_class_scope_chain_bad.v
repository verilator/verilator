// DESCRIPTION: Verilator: Verilog Test module
//
// Error cases for chained class scope resolution in type position.  Each stage
// of `pkg::cls::t` can fail to resolve; the diagnostic should name the segment
// that actually failed, and should not also emit the "Multiple '::'" message.
//
// Arbitrarily deep nesting is supported; if an intermediate segment is not a
// class or package, it should receive the same lookup diagnostic as any other
// unresolved scope.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package P;
  class K;
    typedef logic [7:0] t;
  endclass
endpackage

module t;
  // Inner name is not a member of the (resolved) class
  P::K::nosuch a;
  // Middle scope does not exist
  P::NoSuchClass::t b;
  // Outer scope does not exist
  NoSuchPkg::K::t c;
  // Deeper than one nested scope is still unsupported
  P::K::t::deeper d;
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
