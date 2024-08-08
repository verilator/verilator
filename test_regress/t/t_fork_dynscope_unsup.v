// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  bit p = 0, q = 0;

  initial begin
    t1(p);
    t2(q);
  end

  task t1(inout p);
    fork
      p = #1 1;
    join_none
  endtask

  task t2(output q);
    q <= #1 1;
  endtask
endmodule
