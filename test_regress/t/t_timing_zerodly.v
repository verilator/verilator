// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  static task fork_w_zerodly(longint unsigned current_time);
    bit my_bit;
    bit zero_dly_first = 0;
    // Th code below relies on Verilator's deterministic scheduler and is not
    // compatible across different simulators.
    //
    // The `zero_dly` block is going to be executed first and then suspended at the #0 delay.
    // Then the `finish_before` block is going to be executed. Once that happens, the
    // execution of `zero_dly` block should be resumed, all within a single time-slot.
    //
    // IF THIS TEST FAILS AFTER CHANGES TO VERILATOR'S SCHEDULER, IT DOESN'T NECESSARILY
    // MEAN THE CHANGES ARE WRONG.
    fork
      begin : zero_dly
        zero_dly_first = 1;
        #0;
        if (current_time != $time) $stop;
        if (my_bit == 0) $stop;
      end : zero_dly
      begin : finish_before
        if (!zero_dly_first) $stop;
        my_bit = 1;
      end : finish_before
    join_none
    #1 $display("After fork."); // Check if there's no skipped coroutine
  endtask
endclass

module test();
  initial begin
    Foo::fork_w_zerodly($time);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
