// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  initial begin
    if (a_task(1'b0)) $stop;  // <--- Bad: Calling task _as_ function
  end

  task a_task;
    input ign;
  endtask

endmodule
