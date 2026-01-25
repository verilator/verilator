// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface mem_if #(
    int unsigned ADDR_SIZE = 16
);
endinterface

module t;
  class Cls #(
      type T = int
  );
  endclass

  // Note the referred-to virtual class is only used here, not instantiated
  typedef Cls#(virtual mem_if #(8)) cls_mem_if_t;
  typedef Cls#(virtual mem_if #()) cls_def_if_t;

  initial begin
    cls_mem_if_t c;
    cls_def_if_t d;
    c = new;
    d = new;
    $finish;
  end

endmodule
