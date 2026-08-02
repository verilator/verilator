// DESCRIPTION: Verilator: Verify that implicit-default and explicit-equivalent
// class type parameters resolve to the same specialization.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

package p;
  class W #(
      type T = int
  );
    T v;
  endclass

  class Holder #(
      type U = W#()
  );
    U u;
  endclass

  typedef W#() W_default_t;

  class AliasHolder #(
      type U = W_default_t
  );
    U u;
  endclass

  class V #(
      int A = 3,
      int B = A + 1
  );
    int marker;
  endclass

  class NestedHolder #(
      type U = V#()
  );
    U u;
  endclass

  typedef Holder#() H_imp_t;  // implicit default
  typedef Holder#(W#(int)) H_exp_t;  // explicit equivalent default
  typedef AliasHolder#() AH_imp_t;  // implicit aliased default
  typedef AliasHolder#(W#(int)) AH_exp_t;  // explicit equivalent default
  typedef NestedHolder#() NH_imp_t;  // nested implicit dependent defaults
  typedef NestedHolder#(V#(.A(3))) NH_exp_t;  // explicit nested reference, implicit B
endpackage

module t;
  p::H_imp_t imp;
  p::H_exp_t exp;
  p::AH_imp_t alias_imp;
  p::AH_exp_t alias_exp;
  p::NH_imp_t nested_imp;
  p::NH_exp_t nested_exp;

  initial begin
    imp = new;
    // verilator lint_off CASTCONST
    // verilator lint_off WIDTHTRUNC
    if (!$cast(exp, imp)) begin
      // verilator lint_on WIDTHTRUNC
      // verilator lint_on CASTCONST
      $display("WRONG_TYPE");
      $fatal;
    end
    alias_imp = new;
    // verilator lint_off CASTCONST
    // verilator lint_off WIDTHTRUNC
    if (!$cast(alias_exp, alias_imp)) begin
      // verilator lint_on WIDTHTRUNC
      // verilator lint_on CASTCONST
      $display("WRONG_ALIAS_TYPE");
      $fatal;
    end
    nested_imp = new;
    // verilator lint_off CASTCONST
    // verilator lint_off WIDTHTRUNC
    if (!$cast(nested_exp, nested_imp)) begin
      // verilator lint_on WIDTHTRUNC
      // verilator lint_on CASTCONST
      $display("WRONG_NESTED_TYPE");
      $fatal;
    end
    $write("*-* All Coverage Coverage *-*\n");
    $finish;
  end
endmodule
