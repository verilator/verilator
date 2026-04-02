// DESCRIPTION: Verilator: Verify that implicit-default and explicit-equivalent
// class type parameters resolve to the same specialization.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

package p;
  class W #(type T = int);
    T v;
  endclass

  class Holder #(type U = W#());
    U u;
  endclass

  typedef Holder#()         H_imp_t;       // implicit default
  typedef Holder#(W#(int))  H_exp_t;       // explicit equivalent default
endpackage

module t;
  p::H_imp_t imp;
  p::H_exp_t exp;

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
    $write("*-* All Coverage Coverage *-*\n");
    $finish;
  end
endmodule
