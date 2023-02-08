// DESCRIPTION: Verilator: constant string functions
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t ();

   function automatic string foo_func();
      foo_func = "FOO";
   endfunction

   localparam string the_foo = foo_func();

   initial begin
      if (the_foo != "FOO") $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
