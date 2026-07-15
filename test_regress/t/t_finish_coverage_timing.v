// DESCRIPTION: Verilator: Finish-aware coverage timing boundaries
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  int delayed_count;
  bit event_hit_trigger;
  bit event_miss_trigger;
  int event_hit_count;
  int event_miss_count;
  int unrelated_count;
  bit wait_hit_trigger;
  bit wait_miss_trigger;
  int wait_hit_count;
  int wait_miss_count;

  task automatic maybe_finish(input bit finish_now);
    if (finish_now) $finish;
  endtask

  initial begin
    #1 unrelated_count++;  // COVER_TIMING_LINE COVER_TIMING_HIT
    #1 unrelated_count++;  // COVER_TIMING_LINE COVER_TIMING_HIT
  end

  initial begin
    #10
      delayed_count++;  // COVER_TIMING_MISS
    maybe_finish(0);
  end

  initial begin
    @(posedge event_hit_trigger)
      event_hit_count++;  // COVER_TIMING_HIT
    maybe_finish(0);
  end

  initial begin
    @(posedge event_miss_trigger)
      event_miss_count++;  // COVER_TIMING_MISS
    maybe_finish(0);
  end

  initial begin
    wait (wait_hit_trigger)
      wait_hit_count++;  // COVER_TIMING_HIT
    maybe_finish(0);
  end

  initial begin
    wait (wait_miss_trigger)
      wait_miss_count++;  // COVER_TIMING_MISS
    maybe_finish(0);
  end

  initial begin
    #1;
    event_hit_trigger = 1;
    wait_hit_trigger = 1;
  end

  initial begin
    #3;
    `checkd(unrelated_count, 2);
    `checkd(delayed_count, 0);
    `checkd(event_hit_count, 1);
    `checkd(event_miss_count, 0);
    `checkd(wait_hit_count, 1);
    `checkd(wait_miss_count, 0);
    maybe_finish(1);
  end

  final $write("*-* All Finished *-*\n");
endmodule
