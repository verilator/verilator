// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer i;
   reg [6:0] w7;
   reg [14:0] w15;
   reg [30:0] w31;
   reg [62:0] w63;
   reg [94:0] w95;

   integer      cyc = 0;

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d\n", $time, cyc);
`endif
      cyc <= cyc + 1;
      if (cyc==0) begin
         // Setup
         w7 = {7{1'b1}};
         w15 = {15{1'b1}};
         w31 = {31{1'b1}};
         w63 = {63{1'b1}};
         w95 = {95{1'b1}};
      end
      else if (cyc == 1) begin
         if (w7++ != {7{1'b1}}) $stop;
         if (w7 != {7{1'b0}}) $stop;
         if (w7-- != {7{1'b0}}) $stop;
         if (w7 != {7{1'b1}}) $stop;
         if (++w7 != {7{1'b0}}) $stop;
         if (w7 != {7{1'b0}}) $stop;
         if (--w7 != {7{1'b1}}) $stop;
         if (w7 != {7{1'b1}}) $stop;

         if (w15++ != {15{1'b1}}) $stop;
         if (w15 != {15{1'b0}}) $stop;
         if (w15-- != {15{1'b0}}) $stop;
         if (w15 != {15{1'b1}}) $stop;
         if (++w15 != {15{1'b0}}) $stop;
         if (w15 != {15{1'b0}}) $stop;
         if (--w15 != {15{1'b1}}) $stop;
         if (w15 != {15{1'b1}}) $stop;

         if (w31++ != {31{1'b1}}) $stop;
         if (w31 != {31{1'b0}}) $stop;
         if (w31-- != {31{1'b0}}) $stop;
         if (w31 != {31{1'b1}}) $stop;
         if (++w31 != {31{1'b0}}) $stop;
         if (w31 != {31{1'b0}}) $stop;
         if (--w31 != {31{1'b1}}) $stop;
         if (w31 != {31{1'b1}}) $stop;

         if (w63++ != {63{1'b1}}) $stop;
         if (w63 != {63{1'b0}}) $stop;
         if (w63-- != {63{1'b0}}) $stop;
         if (w63 != {63{1'b1}}) $stop;
         if (++w63 != {63{1'b0}}) $stop;
         if (w63 != {63{1'b0}}) $stop;
         if (--w63 != {63{1'b1}}) $stop;
         if (w63 != {63{1'b1}}) $stop;

         if (w95++ != {95{1'b1}}) $stop;
         if (w95 != {95{1'b0}}) $stop;
         if (w95-- != {95{1'b0}}) $stop;
         if (w95 != {95{1'b1}}) $stop;
         if (++w95 != {95{1'b0}}) $stop;
         if (w95 != {95{1'b0}}) $stop;
         if (--w95 != {95{1'b1}}) $stop;
         if (w95 != {95{1'b1}}) $stop;
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
