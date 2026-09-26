// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// An array of interface references, plus a scalar one, in a leaf module.
// Nothing is named "arr"; each element is its own reference "arr[N]", and a
// tool discovers them by iterating the module's vpiInternalScope children.

interface SomeIntf;

  logic [31:0] some_intf_var;

  modport SomeModport(inout some_intf_var);

endinterface

module Foo (
    SomeIntf.SomeModport arr[4],
    SomeIntf plain
);

  logic [31:0] foo_var;

  always_comb
    foo_var = arr[0].some_intf_var ^ arr[1].some_intf_var ^ arr[2].some_intf_var
              ^ arr[3].some_intf_var ^ plain.some_intf_var;

endmodule

module t;

  SomeIntf top_arr[4] ();
  SomeIntf top_plain ();

  Foo foo (
      .arr  (top_arr),
      .plain(top_plain)
  );

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule : t
