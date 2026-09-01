// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); $stop; end while(0);
// verilog_format: on

module kill_sibling;
  bit proc_a_hanged = 0;
  bit proc_a_killed = 0;
  bit proc_b_finished = 0;
  bit joined = 0;

  initial begin : kill_hanged_sibling
    fork
      process p;
      begin : process_a
        p = process::self();
        proc_a_hanged = 1;
        wait (0);
        $fatal(2, "shouldn't get here");
      end
      begin : process_b
        #2;
        p.kill();
        proc_a_killed = 1;
        #5;
        proc_b_finished = 1;
      end
    join_any
    joined = 1;
  end

  initial begin
    #0;
    `checkd(proc_a_hanged, 1);
    `checkd(proc_a_killed, 0);
    `checkd(proc_b_finished, 0);
    `checkd(joined, 0);
    #2;
    #0;
    `checkd(proc_a_hanged, 1);
    `checkd(proc_a_killed, 1);
    `checkd(proc_b_finished, 0);
    `checkd(joined, 1);
    #5;
    #0;
    `checkd(proc_a_hanged, 1);
    `checkd(proc_a_killed, 1);
    `checkd(proc_b_finished, 1);
    `checkd(joined, 1);
  end
endmodule

module kill_proc_next_cyc;
  process p;
  bit proc_a_hanged = 0;
  bit proc_a_killed = 0;
  bit joined = 0;

  initial begin
    #1;
    p.kill();
    proc_a_killed = 1;
  end

  initial begin
    fork
      begin : process_a
        p = process::self();
        proc_a_hanged = 1;
        wait (0);
        $fatal(2, "shouldn't get here");
      end
    join_any
    joined = 1;
  end

  initial begin
    #0;
    `checkd(proc_a_hanged, 1);
    `checkd(proc_a_killed, 0);
    `checkd(joined, 0);
    #1;
    #0;
    `checkd(proc_a_hanged, 1);
    `checkd(proc_a_killed, 1);
    `checkd(joined, 1);
  end
endmodule

module kill_proc_same_cyc;
  process p;
  bit proc_a_hanged = 0;
  bit proc_a_killed = 0;
  bit joined = 0;

  initial begin
    #0;  // Do it same cycle, just after process_a hanged
    p.kill();
    proc_a_killed = 1;
  end

  initial begin
    fork
      begin : process_a
        p = process::self();
        proc_a_hanged = 1;
        wait (0);
        $fatal(2, "shouldn't get here");
      end
    join_any
    joined = 1;
  end

  initial begin
    #0;
    #0;
    `checkd(proc_a_hanged, 1);
    `checkd(proc_a_killed, 1);
    `checkd(joined, 1);
  end
endmodule

module disable_fork;
  bit hanged = 0;
  bit finished = 0;
  bit joined = 0;
  bit disabled_fork = 0;
  initial begin
    fork
      begin
        hanged = 1;
        wait (0);
      end
      begin
        finished = 1;
      end
    join_any
    joined = 1;
    #5;
    disable fork;
    disabled_fork = 1;
  end

  initial begin
    #0;
    `checkd(hanged, 1);
    `checkd(finished, 1);
    `checkd(joined, 1);
    `checkd(disabled_fork, 0);
    #5;
    #0;
    `checkd(hanged, 1);
    `checkd(finished, 1);
    `checkd(joined, 1);
    `checkd(disabled_fork, 1);
  end
endmodule

module t;
  kill_sibling kill_sibling ();
  kill_proc_next_cyc kill_proc_next_cyc ();
  kill_proc_same_cyc kill_proc_same_cyc ();
  disable_fork disable_fork ();

  initial begin
    #15;
    $info("*-* All Finished *-*");
    $finish;
  end
endmodule
