// DESCRIPTION: Verilator: constant string functions
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t ();

   function automatic string foo_func();
      foo_func = "FOO";
      foo_func = $sformatf("%sBAR", foo_func);
      for (int i = 0; i < 4; i++)
         foo_func = $sformatf("%s%0d", foo_func, i);
   endfunction

   localparam string the_foo = foo_func();

   initial begin
      if (the_foo != "FOOBAR0123") $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
