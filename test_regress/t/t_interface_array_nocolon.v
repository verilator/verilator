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

   // Should not cause LITENDIAN warning, as no harm in array selections.
   // verilator lint_on LITENDIAN
   foo_intf foo1 [N] (.x(1'b1));
   foo_subm sub1 [N] (.x(1'b1));

   // Will cause LITENDIAN warning?
   // verilator lint_off LITENDIAN
   foo_intf foos [N] (.x(X));
   foo_intf fool [1:3] (.x(X));
   foo_intf foom [3:1] (.x(X));

   foo_subm subs [N] (.x(X));
   foo_subm subl [1:3] (.x(X));
   foo_subm subm [3:1] (.x(X));

   initial begin
      // Check numbering with 0 first
      // NC has a bug here
      if (foos[0].x !== 1'b1) $stop;
      if (foos[1].x !== 1'b1) $stop;
      if (foos[2].x !== 1'b0) $stop;
      //
      if (fool[1].x !== 1'b1) $stop;
      if (fool[2].x !== 1'b1) $stop;
      if (fool[3].x !== 1'b0) $stop;
      //
      if (foom[1].x !== 1'b0) $stop;
      if (foom[2].x !== 1'b1) $stop;
      if (foom[3].x !== 1'b1) $stop;
      //
      if (subs[0].x !== 1'b1) $stop;
      if (subs[1].x !== 1'b1) $stop;
      if (subs[2].x !== 1'b0) $stop;
      //
      if (subl[1].x !== 1'b1) $stop;
      if (subl[2].x !== 1'b1) $stop;
      if (subl[3].x !== 1'b0) $stop;
      //
      if (subm[1].x !== 1'b0) $stop;
      if (subm[2].x !== 1'b1) $stop;
      if (subm[3].x !== 1'b1) $stop;
      //
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
