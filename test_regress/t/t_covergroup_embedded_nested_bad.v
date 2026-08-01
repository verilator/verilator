// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Outer;
  bit [3:0] outer_value;

  class CoverpointInner;
    covergroup cg;
      cp: coverpoint outer_value;
    endgroup

    function new();
      cg = new;
    endfunction
  endclass

  class IffInner;
    bit [3:0] inner_value;

    covergroup cg;
      cp: coverpoint inner_value iff (outer_value != 0);
    endgroup

    function new();
      cg = new;
    endfunction
  endclass
endclass

module t;
  Outer::CoverpointInner coverpoint_inner;
  Outer::IffInner iff_inner;

  initial begin
    coverpoint_inner = new;
    iff_inner = new;
  end
endmodule
