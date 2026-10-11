// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) \
  do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0)
// verilog_format: on

module t;
  bit clk;
  bit flag;
  bit via_delay, via_event, via_wait, via_join, via_grandchild;
  bit orphan_ran;
  bit self_child_ran, self_resumed;
  process parent;
  process finished;

  always #5 clk = ~clk;

  initial begin
    fork
      begin
        parent = process::self();
        fork
          #10 via_delay = 1'b1;
          @(posedge clk) via_event = 1'b1;
          begin wait (flag); via_wait = 1'b1; end
          begin fork #10 via_join = 1'b1; join end
          begin
            fork #10 via_grandchild = 1'b1; join_none
            wait (0);
          end
        join_none
        wait (0);  // Keep the parent alive until it is killed
      end
    join_none

    fork
      begin
        finished = process::self();
        fork
          #10 orphan_ran = 1'b1;
        join_none
      end  // Parent finishes here, while its descendant is still alive
    join_none

    // A process killing itself must take its descendants down as well
    fork
      begin
        fork #10 self_child_ran = 1'b1; join_none
        process::self().kill();
        #1;
        self_resumed = 1'b1;
      end
    join_none

    #1;  // Let the processes start and suspend
    `checkd(parent.status(), process::WAITING);
    parent.kill();
    `checkd(parent.status(), process::KILLED);
    flag = 1'b1;  // Would release the waiting descendant had it survived

    // IEEE 1800-2023 9.7: kill() on a FINISHED process still terminates its live
    // descendants
    `checkd(finished.status(), process::FINISHED);
    finished.kill();
    `checkd(finished.status(), process::FINISHED);

    #20;
    `checkd(via_delay, 1'b0);
    `checkd(via_event, 1'b0);
    `checkd(via_wait, 1'b0);
    `checkd(via_join, 1'b0);
    `checkd(via_grandchild, 1'b0);
    `checkd(orphan_ran, 1'b0);
    `checkd(self_child_ran, 1'b0);
    `checkd(self_resumed, 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
