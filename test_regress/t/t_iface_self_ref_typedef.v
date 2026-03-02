// DESCRIPTION: Verilator: Test for self-referential interface typedef
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Self-referential typedef: typedef iface#(T) this_type inside interface iface
interface my_iface #(type T = logic);
  typedef my_iface #(T) self_t;
  T data;
endinterface

module t ();
  my_iface #(logic [7:0]) if0 ();

  initial begin
    if0.data = 8'hAB;
    if ($bits(if0.data) != 8) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
