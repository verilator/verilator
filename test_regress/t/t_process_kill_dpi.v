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
  process victim;
  process caller;
  int returned;
  int value = -1;
  bit caller_after;

  import "DPI-C" context function int call_kill(bit self);
  import "DPI-C" context task call_kill_task();
  export "DPI-C" function kill_from_export;

  // Killing another process returns normally. Killing the DPI caller stops both the export
  // and the caller, and the import's result is not assigned.
  function automatic void kill_from_export(bit self);
    if (self) caller.kill();
    else victim.kill();
    ++returned;
  endfunction

  initial begin
    fork
      begin
        victim = process::self();
        #10;
      end
    join_none
    #1;
    value = call_kill(0);
    `checkd(value, 42);
    `checkd(victim.status(), process::KILLED);
    `checkd(returned, 1);

    for (int variant = 0; variant < 2; ++variant) begin
      value = -1;
      caller_after = 1'b0;
      fork
        begin
          caller = process::self();
          if (variant == 0) value = call_kill(1);
          else call_kill_task();
          caller_after = 1'b1;
        end
      join_none
      #1;
      `checkd(caller.status(), process::KILLED);
      `checkd(caller_after, 1'b0);
      `checkd(value, -1);
      `checkd(returned, 1);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
