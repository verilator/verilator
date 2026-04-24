// DESCRIPTION: Verilator: dynamic wait on stale class event
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class EventHolder;
   event ev;
   time t_wait = '0;

   task wait_once;
      @ev;
      t_wait = $time;
   endtask
endclass

module t;
   EventHolder h;

   initial begin
      h = new;

      // Leave the event in the fired state before a class-method event control
      // starts. Dynamic waits must pre-clear this stale state before evaluating.
      ->h.ev;
      #10;

      fork
         begin
            #10 ->h.ev;
         end
         begin
            h.wait_once;
         end
      join

      if (h.t_wait != 20) begin
         $display("%%Error: wait time=%0d expected=20", h.t_wait);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
