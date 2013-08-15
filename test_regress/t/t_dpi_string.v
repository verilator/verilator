// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

module t ();

   import "DPI-C" function int dpii_string(input string DSM_NAME);

   generate
      begin : DSM
	 string SOME_STRING;
      end
   endgenerate

   initial begin
      $sformat(DSM.SOME_STRING, "%m");
      if (dpii_string(DSM.SOME_STRING) != 5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
