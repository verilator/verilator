// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

interface SomeIntf;

  logic [31:0] some_intf_var;

  modport SomeModport(inout some_intf_var);

endinterface

module Foo (
    SomeIntf.SomeModport intf_ref,
    SomeIntf plain_ref
);

  logic [31:0] foo_saw_some;
  logic [31:0] foo_saw_plain;

  always_comb foo_saw_some = intf_ref.some_intf_var;
  always_comb foo_saw_plain = plain_ref.some_intf_var;

endmodule

module t;

  SomeIntf concrete_intf ();

  Foo foo (
      .intf_ref (concrete_intf),
      .plain_ref(concrete_intf)
  );

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule : t
