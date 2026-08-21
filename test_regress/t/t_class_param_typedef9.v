// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// A typedef of a parameterized class produces an AstRefDType whose skipRefp()
// is the AstClassRefDType, which V3Param also reaches directly.  This validates
// that the AstClassRefDType is not enqueued to mcell_ps twice
class Wrap #(
    type T = int
);
  int m_v;
endclass

class L0;
  typedef Wrap#(L0) w_t;
  w_t m_w;
  function new();
    m_w = new;
    m_w.m_v = 42;
  endfunction
endclass

module t;
  L0 l0;
  initial begin
    l0 = new;
    if (l0.m_w.m_v != 42) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
