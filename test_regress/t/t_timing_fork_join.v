// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   event event1;
   event event2;
   event event3;

   initial begin
      fork
         begin /*empty*/ end
         #8 $write("[%0t] fork..join process 1\n", $time);
         #4 $write("[%0t] fork..join process 2\n", $time);
         #2 $write("[%0t] fork..join process 3\n", $time);
         $write("[%0t] fork..join process 4\n", $time);
         begin : fork_in_fork #16
             $write("[%0t] fork in fork starts\n", $time);
             fork
                 #16 $write("[%0t] fork..join process 5\n", $time);
                 #8 $write("[%0t] fork..join process 6\n", $time);
                 #4 $write("[%0t] fork..join process 7\n", $time);
                 $write("[%0t] fork..join process 8\n", $time);
             join
             $write("[%0t] fork..join in fork ends\n", $time);
         end
      join
      #32 $write("[%0t] main process\n", $time);
      fork
         begin
            @event1;
            $write("fork..join_any process 1\n");
            ->event1;
         end
         $write("fork..join_any process 2\n");
      join_any
      $write("back in main process\n");
      #1 ->event1;
      #1 fork
      #2 $write("fork..join_any process 1\n");
         begin
            @event1;
            $write("fork..join_any process 2\n");
            ->event1;
         end
      join_any
      $write("back in main process\n");
      #1 ->event1;
      @event1;
      // Order of triggering:
      // p1->event2  ==>  p2->event3  ==>  p3->event3  ==>  p2->event2  ==>  p1->event3  ==>  p3->event1
      fork
         begin
            #1 $write("fork..join_none process 1\n");
            ->event2;
            @event2 $write("fork..join_none process 1 again\n");
            #1 ->event3;
         end
         begin
            @event2 $write("fork..join_none process 2\n");
            #1 ->event3;
            @event3 $write("fork..join_none process 2 again\n");
            #1 ->event2;
         end
         begin
            @event3 $write("fork..join_none process 3\n");
            #1 ->event3;
            @event3 $write("fork..join_none process 3 again\n");
            ->event1;
         end
      join_none
      $write("in main process\n");
      @event1;
      $write("*-* All Finished *-*\n");
      $finish;
    end
    initial #100 $stop; // timeout

    // Test optimized-out fork statements:
    reg a;
    initial fork a = 1; join
endmodule
