// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  int seen[2];
  int seen_join_any[2];
  int seen_join[2];
  int seen_deep[2];
  int seen_member[2];
  int member_id;
  static int static_seen[2];

  // Every call must give its fork its own copy of 'id'
  function void launch(int id);
    fork
      fork
        #1 seen[id] = 1;
      join_none
    join_none
  endfunction

  // The inner join_any must not stop the caller from re-entering
  task launch_join_any(int id);
    fork
      fork
        #1 seen_join_any[id] = 1;
      join_any
    join_none
  endtask

  // Same, for a plain inner join
  task launch_join(int id);
    fork
      fork
        #1 seen_join[id] = 1;
      join
    join_none
  endtask

  // Three fork levels: the outer and the middle branch both capture 'id'
  function void launch_deep(int id);
    fork
      fork
        fork
          #1 seen_deep[id] = 1;
        join_none
      join_none
    join_none
  endfunction

  // Capture a class member, not an argument
  function void launch_member();
    automatic int local_id = member_id;
    fork
      fork
        #1 seen_member[local_id] = 1;
      join_none
    join_none
  endfunction

  // Same, in a static method
  static function void static_launch(int id);
    fork
      fork
        #1 static_seen[id] = 1;
      join_none
    join_none
  endfunction
endclass

module t;
  Cls c = new;

  initial begin
    c.launch(0);  // Both forks are still waiting on #1 ...
    c.launch(1);  // ... when 'id' is set up for the second one
    c.launch_join_any(0);
    c.launch_join_any(1);
    c.launch_join(0);
    c.launch_join(1);
    c.launch_deep(0);
    c.launch_deep(1);
    c.member_id = 0;
    c.launch_member();
    c.member_id = 1;  // The first fork must still see 0
    c.launch_member();
    Cls::static_launch(0);
    Cls::static_launch(1);
    #2;
    `checkd(c.seen[0], 1);
    `checkd(c.seen[1], 1);
    `checkd(c.seen_join_any[0], 1);
    `checkd(c.seen_join_any[1], 1);
    `checkd(c.seen_join[0], 1);
    `checkd(c.seen_join[1], 1);
    `checkd(c.seen_deep[0], 1);
    `checkd(c.seen_deep[1], 1);
    `checkd(c.seen_member[0], 1);
    `checkd(c.seen_member[1], 1);
    `checkd(Cls::static_seen[0], 1);
    `checkd(Cls::static_seen[1], 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
