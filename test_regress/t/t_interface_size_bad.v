// DESCRIPTION: Verilator: Demonstrate deferred linking error messages
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2017 Johan Bjork
// SPDX-License-Identifier: CC0-1.0

interface foo_intf;
  logic a;
endinterface

module t;
  localparam N = 4;
  foo_intf foo4[N-1:0] ();
  foo_intf foo6[5:0] ();

  baz baz4_inst (.foo(foo4));
  baz baz6_inst (.foo(foo6));

  // Multi dimensional, each dimension must match
  foo_intf foo2x4[1:0][3:0] ();
  foo_intf foo3x3[2:0][2:0] ();
  foo_intf foo2x5[1:0][4:0] ();
  baz2 baz2x4_inst (.foo(foo2x4));
  baz2 baz3x3_inst (.foo(foo3x3));
  baz2 baz6r_inst (.foo(foo6));
  baz baz2x5_inst (.foo(foo2x5));

  // Instance array, leading dimension must match the instance array
  baz baz_arr_inst[1:0] (.foo(foo3x3));

endmodule

module baz (
    foo_intf foo[4:0]
);
endmodule

module baz2 (
    foo_intf foo[1:0][2:0]
);
endmodule
