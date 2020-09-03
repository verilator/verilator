// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   function automatic string foo(int i);
      return $sformatf("'%d'", i);  // %0d does not work here
   endfunction
   real r = 1.234;
   string bar = foo(1);
   localparam string pbar = foo(1);
   initial begin
      $write("String: "); $display("'          1'");
      $write("foo(1): "); $display(foo(1));
      $write("s f(1): "); $display("%s", foo(1));
      $write("s parm: "); $display("%s", pbar);
      $write("s strg: "); $display("%s", bar);
      $write("r: "); $display(r);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
