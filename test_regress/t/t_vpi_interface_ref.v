// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Test VPI access to an interface reference port.  A reference is found by
// its fully qualified path, or relative to a handle for the instance that
// declares it.  Interface variables are not accessed through the reference
// itself; vpi_handle(vpiActual, ...) reaches the concrete interface, or the
// modport for a modport-typed port, and the variables are accessed there.

interface SomeIntf;

  logic [31:0] some_intf_var;
  logic [31:0] other_intf_var;

  // inout, as the VPI test writes as well as reads through the reference
  modport SomeModport(inout some_intf_var, inout other_intf_var);

endinterface

// Deepest module, reached via "t.bar.foo".  plain_ref is a plain interface
// port with no modport, whose vpiActual is the interface itself rather than a
// modport; intf_ref is modport-typed.
module Foo (
    SomeIntf.SomeModport intf_ref,
    SomeIntf plain_ref
);

  logic [31:0] foo_saw_some;
  logic [31:0] foo_saw_other;
  logic [31:0] foo_saw_plain;

  // Read the interface variables through the interface reference
  always_comb foo_saw_some = intf_ref.some_intf_var;
  always_comb foo_saw_other = intf_ref.other_intf_var;
  always_comb foo_saw_plain = plain_ref.some_intf_var;

endmodule

// Intermediate module, so the interface reference is passed down a level
module Bar (
    SomeIntf.SomeModport intf_ref,
    SomeIntf plain_ref
);

  Foo foo (
      .intf_ref (intf_ref),
      .plain_ref(plain_ref)
  );

endmodule

// top_collide is a port, so it lands in the TOP scope.  A name looked up
// relative to an interface reference or modport must not fall back to
// searching there, which would return this unrelated object.
module t (
    input logic [31:0] top_collide
);

  SomeIntf concrete_intf ();

  Bar bar (
      .intf_ref (concrete_intf),
      .plain_ref(concrete_intf)
  );

  // The C code registers a value change callback on this, and runs mon_check()
  // when it changes.  Write it immediately before the #1 below, so that every
  // value mon_check() reads is already seeded.
  logic run_mon_check = 1'b0;

  initial begin
    concrete_intf.some_intf_var  = 32'h1111_2222;
    concrete_intf.other_intf_var = 32'h3333_4444;

    run_mon_check = 1'b1;
    #1;

    // mon_check() wrote these via vpiActual of the interface references
    if (concrete_intf.some_intf_var != 32'hfeed_face) begin
      $write("%%Error: some_intf_var = %h\n", concrete_intf.some_intf_var);
      $stop;
    end
    if (concrete_intf.other_intf_var != 32'hdead_beef) begin
      $write("%%Error: other_intf_var = %h\n", concrete_intf.other_intf_var);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule : t
