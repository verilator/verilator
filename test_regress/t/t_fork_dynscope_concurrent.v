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
  static int static_seen[2];

  // Every call must give its fork its own copy of 'id'
  function void launch(int id);
    fork
      fork
        #1 seen[id] = 1;
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
    Cls::static_launch(0);
    Cls::static_launch(1);
    #2;
    `checkd(c.seen[0], 1);
    `checkd(c.seen[1], 1);
    `checkd(Cls::static_seen[0], 1);
    `checkd(Cls::static_seen[1], 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
