// DESCRIPTION: Verilator: Connecting an interface array slice to a module's portmap
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

interface foo_intf;
   logic a;

   modport m(input a);
endinterface

module foo_mod
  (
   foo_intf foo,
   foo_intf.m bars[4]
   );
endmodule

module t (/*AUTOARG*/);

   localparam N = 4;

   foo_intf foos [N-1:0] ();
   foo_intf bars [N] ();
   //foo_intf foos ();

   foo_mod
     foo_mod
       (
        .foo (foos[2]),
    .bars (bars)
        //.foo (foos)
        );

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
