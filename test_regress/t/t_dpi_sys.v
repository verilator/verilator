// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

// Global is the most likely usage scenario
import "DPI-C" dpii_sys_task = function void \$dpii_sys (integer i);
import "DPI-C" dpii_sys_func = function int \$dpii_func (integer i);

module t ();

`ifndef verilator
   `error "Only Verilator supports PLI-ish DPI calls."
`endif

   initial begin
      $dpii_sys(1);
      if ($dpii_func(2) != 3) $stop;
      $dpii_sys(10);
      if ($dpii_func(2) != 12) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
