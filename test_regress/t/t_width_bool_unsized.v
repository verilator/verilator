// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// A Boolean operand is reduced to one bit by V3Width::iterateCheckBool.  A conditional
// expression with a literal arm is 'unsized': it fits in one bit, so it keeps its
// nominal 32-bit width.  V3LiftExpr merges the operands of AstLogAnd/AstLogOr into a
// single 1 bit temporary, so an operand left wider than one bit used to trip the width
// check in V3FuncOpt ("Inconsistent assignment").  It only did so with the wider
// operand on the right, as the left is lifted first and its temporary is then reused
// for the right.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  class C;
    int position;
    int msw;

    // Impure, so V3LiftExpr must lift these out of the expression
    function bit has_next();
      return this.position < this.msw;
    endfunction

    function int next_index();
      return this.position;
    endfunction

    // The ternary is repeated rather than factored into a function, as a function
    // returning bit would be one bit wide and would not reproduce.

    // Unsized operand on the right, which is what used to trip V3FuncOpt.
    function int while_and();
      int n = 0;
      while (this.has_next() && (this.msw > 0 ? this.next_index() < this.msw : 1)) begin
        this.position = this.position + 1;
        n = n + 1;
      end
      return n;
    endfunction

    function int while_or();
      int n = 0;
      while (this.has_next() || (this.msw > 0 ? this.next_index() < this.msw : 1)) begin
        this.position = this.position + 1;
        n = n + 1;
      end
      return n;
    endfunction

    function int if_and();
      if (this.has_next() && (this.msw > 0 ? this.next_index() < this.msw : 1)) return 1;
      return 0;
    endfunction

    function int if_or();
      if (this.has_next() || (this.msw > 0 ? this.next_index() < this.msw : 1)) return 1;
      return 0;
    endfunction

    function int cond_and();
      return (this.has_next() && (this.msw > 0 ? this.next_index() < this.msw : 1)) ? 1 : 0;
    endfunction

    function int cond_or();
      return (this.has_next() || (this.msw > 0 ? this.next_index() < this.msw : 1)) ? 1 : 0;
    endfunction

    function int for_and();
      int n = 0;
      for (int i = 0; this.has_next() && (this.msw > 0 ? this.next_index() < this.msw : 1);
           i = i + 1) begin
        this.position = this.position + 1;
        n = n + 1;
      end
      return n;
    endfunction

    function int for_or();
      int n = 0;
      for (int i = 0; this.has_next() || (this.msw > 0 ? this.next_index() < this.msw : 1);
           i = i + 1) begin
        this.position = this.position + 1;
        n = n + 1;
      end
      return n;
    endfunction

    // Unsized operand on the left, which did not trip V3FuncOpt, but must still be
    // reduced for the operator to see the right value.
    function int lhs_and();
      int n = 0;
      while ((this.msw > 0 ? this.next_index() < this.msw : 1) && this.has_next()) begin
        this.position = this.position + 1;
        n = n + 1;
      end
      return n;
    endfunction

    function int lhs_or();
      int n = 0;
      while ((this.msw > 0 ? this.next_index() < this.msw : 0) || this.has_next()) begin
        this.position = this.position + 1;
        n = n + 1;
      end
      return n;
    endfunction

    // Both operands unsized, and nesting of the two operators.
    function int both_and();
      return ((this.msw > 0 ? this.next_index() < this.msw : 1)
              && (this.msw > 0 ? this.next_index() < this.msw : 1))
                 ? 1
                 : 0;
    endfunction

    function int nested_and();
      if (this.has_next()
          && (this.has_next() && (this.msw > 0 ? this.next_index() < this.msw : 1))) return 1;
      return 0;
    endfunction

    function int three_and();
      if (this.has_next() && (this.msw > 0 ? this.next_index() < this.msw : 1)
          && this.has_next()) return 1;
      return 0;
    endfunction

    // AstLogIf and AstLogEq reach iterateCheckBool through the same visitor as
    // AstLogAnd/AstLogOr, but V3LiftExpr does not merge their operands.  Their operands
    // must reduce without the operator's meaning changing.
    function int logif_val();
      return ((this.msw > 0 ? this.next_index() < this.msw : 1) -> this.has_next()) ? 1 : 0;
    endfunction

    function int logeq_val();
      return ((this.msw > 0 ? this.next_index() < this.msw : 1) <-> this.has_next()) ? 1 : 0;
    endfunction
  endclass

  C c;
  int n;

  // Reduction of untyped expressions, in contexts that do not lift.  These are
  // unsized, so no width warning is issued, and before the fix they were left at
  // their nominal width.
  int rfail = 0;
  int plusarg_val = 0;

  initial begin
    c = new;

    // has_next() is true while position < 5, so each loop runs five times
    c.msw = 5;
    c.position = 0;
    `checkd(c.while_and(), 5);
    `checkd(c.position, 5);
    c.position = 0;
    `checkd(c.while_or(), 5);
    `checkd(c.position, 5);
    c.position = 0;
    `checkd(c.if_and(), 1);
    c.position = 0;
    `checkd(c.if_or(), 1);
    c.position = 0;
    `checkd(c.cond_and(), 1);
    c.position = 0;
    `checkd(c.cond_or(), 1);
    c.position = 0;
    `checkd(c.for_and(), 5);
    `checkd(c.position, 5);
    c.position = 0;
    `checkd(c.for_or(), 5);
    `checkd(c.position, 5);
    c.position = 0;
    `checkd(c.lhs_and(), 5);
    `checkd(c.position, 5);
    c.position = 0;
    `checkd(c.lhs_or(), 5);
    `checkd(c.position, 5);

    c.position = 0;
    `checkd(c.both_and(), 1);
    c.position = 0;
    `checkd(c.nested_and(), 1);
    c.position = 0;
    `checkd(c.three_and(), 1);

    // msw == 0: has_next() is false, and the ternary arms are one (true) or zero
    c.msw = 0;
    c.position = 0;
    `checkd(c.while_and(), 0);
    c.position = 0;
    `checkd(c.if_and(), 0);
    c.position = 0;
    `checkd(c.cond_and(), 0);
    c.position = 0;
    `checkd(c.if_or(), 1);
    c.position = 0;
    `checkd(c.cond_or(), 1);
    c.position = 0;
    `checkd(c.lhs_or(), 0);
    c.position = 0;
    // msw == 0 leaves both arms of the ternary at one
    `checkd(c.both_and(), 1);
    c.position = 0;
    `checkd(c.nested_and(), 0);
    c.position = 0;
    `checkd(c.three_and(), 0);
    // true -> false is false
    c.position = 0;
    `checkd(c.logif_val(), 0);
    // true <-> false is false
    c.position = 0;
    `checkd(c.logeq_val(), 0);

    c.msw = 5;
    c.position = 0;
    `checkd(c.logif_val(), 1);
    c.position = 0;
    `checkd(c.logeq_val(), 1);

    // Untyped expressions, which are unsized, so were previously left at their
    // nominal width
    if ($c(0)) rfail++;
    if ($c(1)) begin
    end else rfail++;
    if ($test$plusargs("NO_SUCH_PLUSARG")) rfail++;
    if ($value$plusargs("NO_SUCH_PLUSARG=%d", plusarg_val)) rfail++;

    `checkd(rfail, 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
