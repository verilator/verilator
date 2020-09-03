// DESCRIPTION: Verilator: Test for warning (not error) on improperly width'ed
// default function argument
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

parameter logic Bar = 1'b1;

function automatic logic calc_y;
   return 1'b1;
endfunction

function automatic logic [1:0] foo
  (
   input logic x = Bar,
   input logic y = calc_y()
   );
   return x + y;
endfunction

module t (/*AUTOARG*/);
   logic [1:0] foo_val;

   initial begin
      foo_val = foo();
      if (foo_val != 2'b10) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
