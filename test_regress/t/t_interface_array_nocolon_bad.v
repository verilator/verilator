// DESCRIPTION: Verilator: Functionally demonstrate an array of interfaces
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Mike Popoloski.
// SPDX-License-Identifier: CC0-1.0

interface foo_intf
  (
   input x
   );
endinterface

module foo_subm
  (
   input x
   );
endmodule

module t ();

   localparam N = 3;

   wire [2:0] X = 3'b110;

   // Will cause LITENDIAN warning?
   foo_intf foos [N] (.x(X)); // bad
   foo_intf fool [1:3] (.x(X)); // bad
   foo_intf foom [3:1] (.x(X)); // ok

   foo_subm subs [N] (.x(X)); // bad
   foo_subm subl [1:3] (.x(X)); // bad
   foo_subm subm [3:1] (.x(X)); // ok
endmodule
