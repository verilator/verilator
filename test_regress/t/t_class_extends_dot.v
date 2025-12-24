// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
  class object_registry #(
      type T = int
  );
  endclass

  class packer;
    typedef object_registry#(packer) type_id;
  endclass
endpackage

package c_pkg;
  import pkg::*;
  class compat_packer extends pkg::packer;
    typedef object_registry#(c_pkg::compat_packer) type_id;
  endclass
endpackage

import pkg::*;
import c_pkg::*;

module t;
  initial begin
    compat_packer c;
    c = new();
    $finish;
  end
endmodule
