// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VCS
 `define NO_SHORTREAL
`endif
`ifdef NC
 `define NO_SHORTREAL
`endif
`ifdef VERILATOR  // Unsupported
 `define NO_SHORTREAL
`endif

module t (/*AUTOARG*/);

   // Note these are NOT pure.
   import "DPI-C" function int dpii_clear ();
   import "DPI-C" function int dpii_count (input int ctr);
   import "DPI-C" function bit dpii_inc0  (input int ctr);
   import "DPI-C" function bit dpii_inc1  (input int ctr);
   import "DPI-C" function bit dpii_incx  (input int ctr, input bit value);

   integer i;
   integer j;
   integer k;
   bit 	   b;
   integer errors;

   task check1(integer line, bit got, bit ex);
      if (got != ex) begin
	 $display("%%Error: Line %0d: Bad result, got=%0d expect=%0d",line,got,ex);
	 errors++;
      end
   endtask
   task check(integer line, int got, int ex);
      if (got != ex) begin
	 $display("%%Error: Line %0d: Bad result, got=%0d expect=%0d",line,got,ex);
	 errors++;
      end
   endtask

   // Test loop
   initial begin
      // bug963
      // verilator lint_off IGNOREDRETURN
      dpii_clear();
      // verilator lint_on IGNOREDRETURN
      j = 0;
      for (i=0; i<64; i++) begin
	 if (i[0])
	   j = 0;
	 else
	   j = {31'b0, dpii_inc1(0)};
	 k = k + j;
      end
      $write("%x\n",k);
      check (`__LINE__, dpii_count(0), 32);

      if (|errors) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
