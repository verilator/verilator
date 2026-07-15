// DESCRIPTION: Verilator: $finish propagation through intra-assignment expressions
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  int callback_after;
  int callback_before;
  time callback_time;
  int caller_after;
  int copyback = 44;
  int data[3] = '{10, 20, 30};
  event lhs_event;
  int index_count;
  time index_time;
  string mode;
  int rhs_count;
  time rhs_time;
  int target = 77;

  function automatic int finish_delay(output int out_value);
    callback_before++;
    callback_time = $time;
    out_value = 1;
    $finish;
    callback_after++;
    return 1;
  endfunction

  function automatic int finish_index(output int out_value);
    callback_before++;
    callback_time = $time;
    out_value = 2;
    $finish;
    callback_after++;
    return 1;
  endfunction

  function automatic int rhs_value();
    rhs_count++;
    rhs_time = $time;
    return 90 + rhs_count;
  endfunction

  function automatic int index_value();
    index_count++;
    index_time = $time;
    return 1;
  endfunction

  initial begin
    #1->lhs_event;
  end

  initial begin
    if (!$value$plusargs("MODE=%s", mode)) mode = "delay";

    if (mode == "delay") begin
      target = #(finish_delay(copyback)) 91;
      caller_after++;
    end
    else if (mode == "lhs_blocking") begin
      data[finish_index(copyback)] = #1 rhs_value();
      caller_after++;
    end
    else if (mode == "lhs_nba") begin
      data[finish_index(copyback)] <= #1 91;
      caller_after++;
    end
    else if (mode == "lhs_event") begin
      data[finish_index(copyback)] = @(lhs_event) rhs_value();
      caller_after++;
    end
    else if (mode == "nba_complete") begin
      data[index_value()] <= #1 rhs_value();
      caller_after++;
    end
    else begin
      $write("%%Error: Unknown mode '%s'\n", mode);
      `stop;
    end
  end

  final begin
    `checkd(callback_before, mode == "nba_complete" ? 0 : 1);
    `checkd(callback_after, 0);
    `checkd(callback_time, mode == "lhs_blocking" || mode == "lhs_event" ? 1 : 0);
    `checkd(rhs_count,
            mode == "lhs_blocking" || mode == "lhs_event" || mode == "nba_complete" ? 1 : 0);
    if (rhs_count != 0) `checkd(rhs_time, 0);
    `checkd(index_count, mode == "nba_complete" ? 1 : 0);
    if (index_count != 0) `checkd(index_time, 0);
    `checkd(copyback, 44);
    `checkd(caller_after, mode == "nba_complete" ? 1 : 0);
    `checkd(target, 77);
    `checkd(data[0], 10);
    `checkd(data[1], mode == "nba_complete" ? 91 : 20);
    `checkd(data[2], 30);
    $write("*-* All Finished *-*\n");
  end
endmodule
