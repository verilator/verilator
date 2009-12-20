// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

module t;

   export "DPI-C" task dpix_twice;
   export "DPI-C" dpix_t_int_renamed = task dpix_twice;
   task dpix_twice(input int i, output int o);  o = ~i; endtask

   initial begin
      $stop;
   end
endmodule
