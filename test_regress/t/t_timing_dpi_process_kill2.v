// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  process victim;
  int export_completed = 0;
  import "DPI-C" context task dpi_import_killed();
  export "DPI-C" v_export_killed = task dpi_export_killed;

  task automatic dpi_export_killed();
    victim = process::self();
    #5;
    export_completed++;
  endtask

  initial begin
    bit caller_completed;

    caller_completed = 0;

    // Kill the caller while its DPI import is suspended in the exported task.
    fork
      begin
        dpi_import_killed();
        caller_completed = 1;
      end
    join_none
    #1;
    victim.kill();
    // Allow the export's pending #5 to expire and the C call to unwind.
    #5;
    `checkd(export_completed, 0);
    `checkd(caller_completed, 0);

    $display("*-* All Finished *-*\n");
    $finish;
  end
endmodule
