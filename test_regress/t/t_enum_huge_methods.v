// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   typedef enum logic [59:0] {
                 E01 = 60'h1,
                 ELARGE = 60'h1234_4567_abcd
                 } my_t;

   integer      cyc = 0;
   my_t e;

   string all;
   int    i_cast;

   // Check runtime
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         // Setup
         e <= E01;
      end
      else if (cyc == 1) begin
         `checks(e.name, "E01");
         `checkh(e.next, ELARGE);
         e <= ELARGE;
      end
      else if (cyc == 3) begin
         `checks(e.name, "ELARGE");
         `checkh(e.next, E01);
         `checkh(e.prev, E01);
         e <= E01;
      end
      //
      else if (cyc == 10) begin
         i_cast <= $cast(e, 60'h1234);
      end
      else if (cyc == 11) begin
         `checkh(i_cast, 0);
         i_cast <= $cast(e, 60'h1);
      end
      else if (cyc == 12) begin
         `checkh(i_cast, 1);
         i_cast <= $cast(e, 60'h1234_4567_abcd);
      end
      else if (cyc == 13) begin
         `checkh(i_cast, 1);
      end
      //
      else if (cyc == 20) begin
         e <= my_t'('h11); // Unknown
      end
      else if (cyc == 21) begin
         `checks(e.name, ""); // Unknown
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
