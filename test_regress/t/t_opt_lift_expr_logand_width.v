// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// The conditional expression is unsized: it fits in one bit, so V3Width leaves
// it at its nominal 32-bit width, while the other operand of the logical
// operator is 1 bit.  V3LiftExpr lifts both operands into one temporary, which
// requires equal widths, and V3FuncOpt then reported "Inconsistent assignment".

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class C;
  int position;
  int msw;

  // Impure, so V3LiftExpr must lift it out
  function bit has_next();
    return this.position < this.msw;
  endfunction

  function int next_index();
    return this.position;
  endfunction

  function int loop_and();
    int count = 0;
    while (this.has_next() && (this.msw > 0 ? this.next_index() < this.msw : 1)) begin
      this.position = this.position + 1;
      count = count + 1;
    end
    return count;
  endfunction

  function int loop_or();
    int count = 0;
    while (this.has_next() || (this.msw > 0 ? this.next_index() < this.msw : 1)) begin
      this.position = this.position + 1;
      count = count + 1;
    end
    return count;
  endfunction
endclass

module t;
  C c;
  int n;

  initial begin
    c = new;

    c.position = 0;
    c.msw = 5;
    n = c.loop_and();
    `checkd(n, 5);
    `checkd(c.position, 5);

    c.position = 0;
    c.msw = 0;
    n = c.loop_and();
    `checkd(n, 0);

    c.position = 0;
    c.msw = 5;
    n = c.loop_or();
    `checkd(n, 5);
    `checkd(c.position, 5);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
