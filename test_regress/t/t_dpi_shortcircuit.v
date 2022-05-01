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
   bit     b;
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
      // Spec says && || -> and ?: short circuit, no others do.
      // Check both constant & non constants.
      dpii_clear();
      check1(`__LINE__, (1'b0 && dpii_inc0(0)), 1'b0);
      check1(`__LINE__, (1'b1 && dpii_inc0(1)), 1'b0);
      check1(`__LINE__, (dpii_inc0(2) && dpii_inc0(3)), 1'b0);
      check1(`__LINE__, (dpii_inc1(4) && dpii_inc0(5)), 1'b0);
      check1(`__LINE__, (dpii_inc0(6) && dpii_inc1(7)), 1'b0);
      check1(`__LINE__, (!(dpii_inc1(8) && dpii_inc1(9))), 1'b0);
      check (`__LINE__, dpii_count(0), 0);
      check (`__LINE__, dpii_count(1), 1);
      check (`__LINE__, dpii_count(2), 1);
      check (`__LINE__, dpii_count(3), 0);
      check (`__LINE__, dpii_count(4), 1);
      check (`__LINE__, dpii_count(5), 1);
      check (`__LINE__, dpii_count(6), 1);
      check (`__LINE__, dpii_count(7), 0);
      check (`__LINE__, dpii_count(8), 1);
      check (`__LINE__, dpii_count(9), 1);
      //
      dpii_clear();
      check1(`__LINE__, (1'b0 & dpii_inc0(0)), 1'b0);
      check1(`__LINE__, (1'b1 & dpii_inc0(1)), 1'b0);
      check1(`__LINE__, (dpii_inc0(2) & dpii_inc0(3)), 1'b0);
      check1(`__LINE__, (dpii_inc1(4) & dpii_inc0(5)), 1'b0);
      check1(`__LINE__, (dpii_inc0(6) & dpii_inc1(7)), 1'b0);
      check1(`__LINE__, (!(dpii_inc1(8) & dpii_inc1(9))), 1'b0);
      check (`__LINE__, dpii_count(0), 1);
      check (`__LINE__, dpii_count(1), 1);
      check (`__LINE__, dpii_count(2), 1);
      check (`__LINE__, dpii_count(3), 1);
      check (`__LINE__, dpii_count(4), 1);
      check (`__LINE__, dpii_count(5), 1);
      check (`__LINE__, dpii_count(6), 1);
      check (`__LINE__, dpii_count(7), 1);
      check (`__LINE__, dpii_count(8), 1);
      check (`__LINE__, dpii_count(9), 1);
      //
      dpii_clear();
      check1(`__LINE__, (1'b0 || dpii_inc0(0)), 1'b0);
      check1(`__LINE__, (1'b1 || dpii_inc0(1)), 1'b1);
      check1(`__LINE__, (dpii_inc0(2) || dpii_inc0(3)), 1'b0);
      check1(`__LINE__, (dpii_inc1(4) || dpii_inc0(5)), 1'b1);
      check1(`__LINE__, (dpii_inc0(6) || dpii_inc1(7)), 1'b1);
      check1(`__LINE__, (!(dpii_inc1(8) || dpii_inc1(9))), 1'b0);
      check (`__LINE__, dpii_count(0), 1);
      check (`__LINE__, dpii_count(1), 0);
      check (`__LINE__, dpii_count(2), 1);
      check (`__LINE__, dpii_count(3), 1);
      check (`__LINE__, dpii_count(4), 1);
      check (`__LINE__, dpii_count(5), 0);
      check (`__LINE__, dpii_count(6), 1);
      check (`__LINE__, dpii_count(7), 1);
      check (`__LINE__, dpii_count(8), 1);
      check (`__LINE__, dpii_count(9), 0);
      //
      dpii_clear();
      check1(`__LINE__, (1'b0 | dpii_inc0(0)), 1'b0);
      check1(`__LINE__, (1'b1 | dpii_inc0(1)), 1'b1);
      check1(`__LINE__, (dpii_inc0(2) | dpii_inc0(3)), 1'b0);
      check1(`__LINE__, (dpii_inc1(4) | dpii_inc0(5)), 1'b1);
      check1(`__LINE__, (dpii_inc0(6) | dpii_inc1(7)), 1'b1);
      check1(`__LINE__, (!(dpii_inc1(8) | dpii_inc1(9))), 1'b0);
      check (`__LINE__, dpii_count(0), 1);
      check (`__LINE__, dpii_count(1), 1);
      check (`__LINE__, dpii_count(2), 1);
      check (`__LINE__, dpii_count(3), 1);
      check (`__LINE__, dpii_count(4), 1);
      check (`__LINE__, dpii_count(5), 1);
      check (`__LINE__, dpii_count(6), 1);
      check (`__LINE__, dpii_count(7), 1);
      check (`__LINE__, dpii_count(8), 1);
      check (`__LINE__, dpii_count(9), 1);
      //
      dpii_clear();
      check1(`__LINE__, (1'b0 -> dpii_inc0(0)), 1'b1);
      check1(`__LINE__, (1'b1 -> dpii_inc0(1)), 1'b0);
      check1(`__LINE__, (dpii_inc0(2) -> dpii_inc0(3)), 1'b1);
      check1(`__LINE__, (dpii_inc1(4) -> dpii_inc0(5)), 1'b0);
      check1(`__LINE__, (dpii_inc0(6) -> dpii_inc1(7)), 1'b1);
      check1(`__LINE__, (!(dpii_inc1(8) -> dpii_inc1(9))), 1'b0);
      check (`__LINE__, dpii_count(0), 0);
      check (`__LINE__, dpii_count(1), 1);
      check (`__LINE__, dpii_count(2), 1);
      check (`__LINE__, dpii_count(3), 0);
      check (`__LINE__, dpii_count(4), 1);
      check (`__LINE__, dpii_count(5), 1);
      check (`__LINE__, dpii_count(6), 1);
      check (`__LINE__, dpii_count(7), 0);
      check (`__LINE__, dpii_count(8), 1);
      check (`__LINE__, dpii_count(9), 1);
      //
      dpii_clear();
      check1(`__LINE__, (1'b0 ? dpii_inc0(0) : dpii_inc0(1)), 1'b0);
      check1(`__LINE__, (1'b1 ? dpii_inc0(2) : dpii_inc0(3)), 1'b0);
      check1(`__LINE__, (dpii_inc0(4) ? dpii_inc0(5) : dpii_inc0(6)), 1'b0);
      check1(`__LINE__, (dpii_inc1(7) ? dpii_inc0(8) : dpii_inc0(9)), 1'b0);
      check (`__LINE__, dpii_count(0), 0);
      check (`__LINE__, dpii_count(1), 1);
      check (`__LINE__, dpii_count(2), 1);
      check (`__LINE__, dpii_count(3), 0);
      check (`__LINE__, dpii_count(4), 1);
      check (`__LINE__, dpii_count(5), 0);
      check (`__LINE__, dpii_count(6), 1);
      check (`__LINE__, dpii_count(7), 1);
      check (`__LINE__, dpii_count(8), 1);
      check (`__LINE__, dpii_count(9), 0);
      //
      dpii_clear();
      check1(`__LINE__, (1'b0 * dpii_inc0(0)), 1'b0);
      check1(`__LINE__, (1'b1 * dpii_inc0(1)), 1'b0);
      check1(`__LINE__, (dpii_inc0(2) * dpii_inc0(3)), 1'b0);
      check1(`__LINE__, (dpii_inc1(4) * dpii_inc0(5)), 1'b0);
      check1(`__LINE__, (dpii_inc0(6) * dpii_inc1(7)), 1'b0);
      check1(`__LINE__, (!(dpii_inc1(8) * dpii_inc1(9))), 1'b0);
      check (`__LINE__, dpii_count(0), 1);
      check (`__LINE__, dpii_count(1), 1);
      check (`__LINE__, dpii_count(2), 1);
      check (`__LINE__, dpii_count(3), 1);
      check (`__LINE__, dpii_count(4), 1);
      check (`__LINE__, dpii_count(5), 1);
      check (`__LINE__, dpii_count(6), 1);
      check (`__LINE__, dpii_count(7), 1);
      check (`__LINE__, dpii_count(8), 1);
      check (`__LINE__, dpii_count(9), 1);
      //
      dpii_clear();
      check1(`__LINE__, (1'b0 + dpii_inc0(0)), 1'b0);
      check1(`__LINE__, (1'b1 + dpii_inc0(1)), 1'b1);
      check1(`__LINE__, (dpii_inc0(2) + dpii_inc0(3)), 1'b0);
      check1(`__LINE__, (dpii_inc1(4) + dpii_inc0(5)), 1'b1);
      check1(`__LINE__, (dpii_inc0(6) + dpii_inc1(7)), 1'b1);
      check1(`__LINE__, (dpii_inc1(8) + dpii_inc1(9)), 1'b0);
      check (`__LINE__, dpii_count(0), 1);
      check (`__LINE__, dpii_count(1), 1);
      check (`__LINE__, dpii_count(2), 1);
      check (`__LINE__, dpii_count(3), 1);
      check (`__LINE__, dpii_count(4), 1);
      check (`__LINE__, dpii_count(5), 1);
      check (`__LINE__, dpii_count(6), 1);
      check (`__LINE__, dpii_count(7), 1);
      check (`__LINE__, dpii_count(8), 1);
      check (`__LINE__, dpii_count(9), 1);
      //
      // Something a lot more complicated
      dpii_clear();
      for (i=0; i<64; i++) begin
         b = ( ((dpii_incx(0,i[0])
                 && (dpii_incx(1,i[1])
                     || dpii_incx(2,i[2])
                     | dpii_incx(3,i[3])))  // | not ||
                || dpii_incx(4,i[4]))
               -> dpii_incx(5,i[5]));
      end
      check (`__LINE__, dpii_count(0), 64);
      check (`__LINE__, dpii_count(1), 32);
      check (`__LINE__, dpii_count(2), 16);
      check (`__LINE__, dpii_count(3), 16);
      check (`__LINE__, dpii_count(4), 36);
      check (`__LINE__, dpii_count(5), 46);

      if (|errors) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
