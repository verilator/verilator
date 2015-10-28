// DESCRIPTION: Verilator: $display() test for %l
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.

module t (/*AUTOARG*/);

   initial begin
      assert (0 == 0) else $fatal(2, "%l %m : %d", 0);
      $display("%l %m");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
