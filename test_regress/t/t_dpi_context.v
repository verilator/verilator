// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

module t ();

   sub a (.inst(1));
   sub b (.inst(2));

   initial begin
      a.test1;
      b.test1;
      a.test2;
      b.test2;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module sub (input integer inst);

   import "DPI-C" context function int dpic_line();
   import "DPI-C" context function int dpic_save(int value);
   import "DPI-C" context function int dpic_restore();

   int result;

   task test1;
      // Check line numbering
`ifndef verilator // Not all sims support SV2009 `__LINE__, and some that do fail the specific-line test
      result = dpic_line(); if (!result) $stop;
`else
      result = dpic_line(); if (result !== `__LINE__) $stop;
      //
      result = dpic_line(); if (result !== `__LINE__) $stop;
`endif

      // Check save-restore
      result = dpic_save(23+inst);
      if (result==0) $stop;
   endtask
   
   task test2;
      if (dpic_restore() != 23+inst) $stop;
   endtask

endmodule
