// DESCRIPTION: Verilator: Simple static elaboration case
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   typedef struct packed {
      logic [ 31 : 0 ] _five;
   } five_t;

   typedef enum {
       LOW_FIVE = 32'hdeadbeef,
       HIGH_FIVE
   } five_style_t;

   function five_t gimme_five ();
      automatic five_t result;

      result._five = 5;

      return result;
   endfunction

   function five_style_t gimme_high_five ();
      automatic five_style_t result;

      result = HIGH_FIVE;

      return result;
   endfunction

   localparam five_t FIVE = gimme_five();
   localparam five_style_t THE_HIGH_FIVE = gimme_high_five();

   initial begin
      if (FIVE._five != 5) begin
         $display("%%Error: Got 0b%b instead of 5", FIVE._five);
         $stop;
      end

      if (THE_HIGH_FIVE != HIGH_FIVE) begin
         $display("%%Error: Got 0b%b instead of HIGH_FIVE", THE_HIGH_FIVE);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
