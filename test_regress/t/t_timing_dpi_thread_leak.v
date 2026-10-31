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

module t ();
  process victim;
  int export_completed = 0;
  int c_completed_expected = 0;
  import "DPI-C" context task dpi_import();
  import "DPI-C" function int live_threads();
  import "DPI-C" function int c_completed();
  export "DPI-C" task dpi_export;
  task automatic dpi_export();
    victim = process::self();
    #5;
    export_completed++;
  endtask
  initial begin
    `checkd(live_threads(), 1);

    repeat (3) begin
      dpi_import();
    end

    // There should be one simulation thread and one worker thread
    `checkd(live_threads(), 2);
    `checkd(export_completed, 6);
    `checkd(c_completed(), 3);

    c_completed_expected = 3;
    repeat (3) begin
      fork
        begin
          dpi_import();
        end
      join_none
      #1;
      // This kills the process mid-execution in dpi_export()
      victim.kill();
      #10;
      // Thread count should be at 2
      `checkd(live_threads(), 2);
      // Killed processes should not reach the end of dpi_export()
      `checkd(export_completed, 6);
      `checkd(c_completed(), ++c_completed_expected);
    end
    $finish;
  end
endmodule
