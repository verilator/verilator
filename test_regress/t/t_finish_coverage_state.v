// DESCRIPTION: Verilator: Coverage state across finish-capable boundaries
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  int normal_after;
  int normal_before;
  int off_after;
  int zero_trip_body;

  task automatic maybe_finish(input bit finish_now);
    if (finish_now) $finish;
  endtask

  function automatic bit finish_capable_false(input bit finish_now);
    if (finish_now) $finish;
    finish_capable_false = 0;
  endfunction

  task automatic exercise();
    normal_before++;  // COVER_LINE_HIT
    maybe_finish(0);  // COVER_LINE_HIT
    normal_after++;  // COVER_LINE_HIT
    while (finish_capable_false(0)) begin  // COVER_LINE_HIT
      zero_trip_body++;  // COVER_LINE_MISS
    end
    normal_after++;  // COVER_LINE_HIT
    // verilator coverage_block_off
    // verilator coverage_block_off
    maybe_finish(0);  // COVER_LINE_OMIT
    off_after++;  // COVER_LINE_OMIT
  endtask

  initial begin
    exercise();
    `checkd(normal_before, 1);
    `checkd(normal_after, 2);
    `checkd(off_after, 1);
    `checkd(zero_trip_body, 0);
    maybe_finish(1);
  end

  final $write("*-* All Finished *-*\n");
endmodule
