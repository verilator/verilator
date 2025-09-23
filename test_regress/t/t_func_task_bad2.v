// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  task a_task;
    input ign;
  endtask

  function void func_calls_task;
    a_task(1'b0);  // <--- Bad: Calling task _from_ function
  endfunction

  function void func_ok;
    fork
      a_task(1'b0);  // ok, and done in UVM
    join_none
  endfunction

endmodule
