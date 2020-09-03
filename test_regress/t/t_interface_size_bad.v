// DESCRIPTION: Verilator: Demonstrate deferred linking error messages
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Johan Bjork.
// SPDX-License-Identifier: CC0-1.0

interface foo_intf;
   logic a;
endinterface

module t (/*AUTOARG*/);
   localparam N = 4;
   foo_intf foo4 [N-1:0] ();
   foo_intf foo6 [5:0] ();

   baz baz4_inst (.foo(foo4));
   baz baz6_inst (.foo(foo6));

endmodule

module baz(foo_intf foo[4:0] );
endmodule
