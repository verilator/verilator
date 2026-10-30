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
  bit after_new;
  process victim;

  class killer;
    function new(process victim);
      victim.kill();
    endfunction
  endclass

  initial begin
    static killer killer_instance;
    fork
      begin
        automatic process p = process::self();
        victim = p;
        killer_instance = new(p);  // Constructor kills its own caller
        after_new = 1'b1;
      end
    join_none
    #1;
    `checkd(victim.status(), process::KILLED);
    `checkd(after_new, 1'b0);
    `checkd(killer_instance == null, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
