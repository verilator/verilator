// DESCRIPTION: Verilator: Reevaluate function and method calls in wait conditions
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class State;
  int value;
  function bit ready();
    return value == 3;
  endfunction
endclass

module t;
  State state;
  process child;
  process killed;
  bit completed;
  bit kill_seen;

  initial begin
    state = new;
    fork
      begin
        fork
          begin
            child = process::self();
            #5;
            state.value = 3;
          end
          begin
            #20;
            `checkd(completed, 1)
          end
        join
      end
      begin
        #1;
        wait (state.ready());
        `checkd($time, 5)
        child.await();
        `checkd($time, 5)
        `checkd(child.status(), process::FINISHED)
        completed = 1;
      end
    join
    fork
      begin
        killed = process::self();
        #100;
        `stop;
      end
      begin
        #2;
        killed.kill();
      end
      begin
        #1;
        killed.await();
        `checkd($time, 22)
        `checkd(killed.status(), process::KILLED)
        kill_seen = 1;
      end
    join
    `checkd(kill_seen, 1)
    $write("*-* All Finished *-*\n");
    $finish;
  end
  initial begin
    #150;
    `stop;
  end
endmodule
