// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef enum {TEN=10,
              ELEVEN=11,
              SIXTEEN=16} enum_t;

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int i;
   int i_const;
   int cyc;
   enum_t en;

   // Constant propagation tests
   initial begin
      en = SIXTEEN;
      i_const = $cast(en, 1);
      if (i_const != 0) $stop;
      if (en != SIXTEEN) $stop;

      en = SIXTEEN;
      i_const = $cast(en, 10);
      if (i_const != 1) $stop;
      if (en != TEN) $stop;
   end

   // Test loop
   always @ (posedge clk) begin
      i = $cast(en, cyc);
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d i=%0d en=%0d\n", $time, cyc, i, en);
`endif
      cyc <= cyc + 1;
      if (cyc == 10) begin
         if (i != 1) $stop;
         if (en != TEN) $stop;
      end
      else if (cyc == 11) begin
         if (i != 1) $stop;
         if (en != ELEVEN) $stop;
      end
      else if (cyc == 12) begin
         if (i != 0) $stop;
         if (en != ELEVEN) $stop;
      end
      else if (cyc == 16) begin
         if (i != 1) $stop;
         if (en != SIXTEEN) $stop;
      end
      else if (cyc == 17) begin
         if (i != 0) $stop;
         if (en != SIXTEEN) $stop;
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
