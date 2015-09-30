// DESCRIPTION: Verilator: Simple static elaboration case
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.

module t (/*AUTOARG*/);

   typedef struct packed {
      logic [ 31 : 0 ] _five;
   } five_t;

   function five_t gimme_five ();
      automatic five_t result;

      result._five = 5;

      return result;
   endfunction

   localparam five_t FIVE = gimme_five();

   initial begin
      if (FIVE._five != 5) begin
         $display("%%Error: Got 0b%b instead of 5", FIVE._five);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
