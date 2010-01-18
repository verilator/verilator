// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

module t ();

`ifndef VERILATOR
   `error "Only Verilator supports PLI-ish DPI calls and sformat conversion."
`endif

   import "DPI-C" context dpii_display_call
     = function void \$dpii_display (input string formatted /*verilator sformat*/ );

   integer a;

   initial begin
      // Check variable width constant string conversions
      $dpii_display("");
      $dpii_display("c");
      $dpii_display("co");
      $dpii_display("cons");
      $dpii_display("constant");
      $dpii_display("constant_value");

      a = $c("10");  // Don't optimize away "a"
      $display     ("one10=%x ",a);  // Check single arg
      $dpii_display("one10=%x ",a);
      $display     ("Mod=%m 16=%d 10=%x ",a,a); // Check multiarg
      $dpii_display("Mod=%m 16=%d 10=%x ",a,a);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
