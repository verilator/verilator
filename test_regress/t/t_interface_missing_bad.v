// DESCRIPTION: Verilator: Missing interface test
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

// Interface intentionally not defined
//interface foo_intf;
//   logic a;
//endinterface

module foo_mod
  (
   foo_intf foo
   );
endmodule

module t (/*AUTOARG*/);

   foo_intf the_foo ();

   foo_mod
     foo_mod
       (
        .foo (the_foo)
        );

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
