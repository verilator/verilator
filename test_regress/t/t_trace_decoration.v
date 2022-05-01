// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   integer      a_very_long_name_which_we_will_hash_eventually=0;

   always @ (posedge clk) begin
      a_very_long_name_which_we_will_hash_eventually <= a_very_long_name_which_we_will_hash_eventually + 1;
      if (a_very_long_name_which_we_will_hash_eventually == 5) begin
         fin();
      end
   end

   task fin;
      $write("*-* All Finished *-*\n");
      $finish;
   endtask

endmodule
