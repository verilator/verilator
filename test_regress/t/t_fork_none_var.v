// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   logic [3:0] m_mask;

   initial begin
      int i;
      int n = 4;
      m_mask = 0;
      fork
         begin
            fork
               begin
                  fork
                     begin
                        for(i = 0; i < n; i++) begin
                           fork
                              automatic int k = i;
                              begin
                                 // see issue #4493
                                 $display("[%0t] start %0d", $time, k);
                                 // UVM's arb_sequence_q[is_relevant_entries[k]].wait_for_relevant();
                                 m_mask[k] = 1;
                                 #1;
                              end
                           join_none
                           wait (m_mask[i]);
                        end
                     end
                  join_any
               end
            join_any
         end
      join

      if (m_mask != {4{1'b1}}) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
