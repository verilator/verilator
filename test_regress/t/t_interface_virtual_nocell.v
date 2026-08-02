// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface mem_if #(
    int unsigned ADDR_SIZE = 16
);
endinterface

interface required_if #(
    type T,
    int W
);
  T data;
endinterface

module t;
  class Cls #(
      type T = int
  );
  endclass

  // Note the referred-to virtual class is only used here, not instantiated
  typedef Cls#(virtual mem_if #(8)) cls_mem_if_t;
  typedef Cls#(virtual mem_if #()) cls_def_if_t;
  typedef Cls#(virtual required_if#(logic [6:0], 7)) cls_required_if_t;

  initial begin
    cls_mem_if_t c;
    cls_def_if_t d;
    cls_required_if_t e;
    c = new;
    d = new;
    e = new;
    $finish;
  end

endmodule
