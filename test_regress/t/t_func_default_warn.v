// DESCRIPTION: Verilator: Test for warning (not error) on improperly width'ed
// default function argument
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

function logic foo
  (
   // Intentionally provide a non-width'ed default value
   // This should warn, not error out
   input logic x = 0
   );
   return x;
endfunction

module t (/*AUTOARG*/);
   logic foo_val;

   initial begin
      foo_val = foo();
      if (foo_val != 1'b0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
