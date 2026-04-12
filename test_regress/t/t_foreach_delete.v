// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`ifdef verilator
 `define no_optimize(v) $c(v)
`else
 `define no_optimize(v) (v)
`endif
// verilog_format: on

// Test that a delete inside a foreach() still visits all indicies.
// IEEE 1800-2023 12.7.3 "If the dimensions of a dynamically sized
// array are changed while iterating over a foreach-loop construct, th
// results are undefined".  However UVM requires delete to work.

module t;

  int map[int];
  int q[$];

  function automatic void map_count;
    int loops;
    map = '{0: `no_optimize(3), 1: 3, 2: 4};
    `checkd(map.size(), 3);

    // Loop without side effects, should not use a changed-loop check
    foreach (map[idx]) begin
      ++loops;
    end
    `checkd(loops, 3);
  endfunction

  function automatic void queue_count;
    int loops;
    q = '{`no_optimize(3), `no_optimize(3), `no_optimize(4)};
    `checkd(q.size(), 3);

    // Loop without side effects, should not use a changed-loop check
    foreach (q[idx]) begin
      ++loops;
    end
    `checkd(loops, 3);
  endfunction

  function automatic void map_delete_end;
    int loops;
    int cnt;
    map = '{0: `no_optimize(3), 1: 3, 2: 4};
    $display("map=%p", map);
    `checkd(map.size(), 3);

    foreach (map[idx]) begin
      if (map[idx] == 4) begin
        cnt++;
        map.delete(idx);
      end
      ++loops;
    end
    $display("map=%p", map);
    `checkd(loops, 3);
    `checkd(cnt, 1);
    `checkd(map.size(), 2);
  endfunction

  function automatic void queue_delete_end;
    int loops;
    int cnt;
    q = '{`no_optimize(3), `no_optimize(3), `no_optimize(4)};
    $display("q=%p", q);
    `checkd(q.size(), 3);

    foreach (q[idx]) begin
      if (q[idx] == 4) begin
        cnt++;
        q.delete(idx);
      end
      ++loops;
    end
    $display("q=%p", q);
    `checkd(loops, 3);
    `checkd(cnt, 1);
    `checkd(q.size(), 2);
  endfunction

  function automatic void map_delete_middle;
    int loops;
    int cnt;
    map = '{0: `no_optimize(3), 1: 3, 2: 4};
    $display("map=%p", map);
    `checkd(map.size(), 3);

    foreach (map[idx]) begin
      if (map[idx] == 3) begin
        cnt++;
        map.delete(idx);
      end
      ++loops;
    end
    $display("map=%p", map);
    `checkd(loops, 3);
    `checkd(cnt, 2);
    `checkd(map.size(), 1);
  endfunction

  function automatic void queue_delete_middle;
    int loops;
    int cnt;
    q = '{`no_optimize(3), `no_optimize(3), `no_optimize(4)};
    $display("q=%p", q);
    `checkd(q.size(), 3);

    foreach (q[idx]) begin
      if (q[idx] == 3) begin
        cnt++;
        q.delete(idx);
      end
      ++loops;
    end
    $display("q=%p", q);
    `checkd(loops, 3);
    `checkd(cnt, 2);
    `checkd(q.size(), 1);
  endfunction

  initial begin
    map_count();
    queue_count();
    map_delete_middle();
    queue_delete_middle();
    map_delete_end();
    queue_delete_end();
    $finish;
  end
endmodule
