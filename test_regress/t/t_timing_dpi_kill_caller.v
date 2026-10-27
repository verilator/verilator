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
  int completed = 0;
  import "DPI-C" context task imp();
  export "DPI-C" task dpi_export;
  task automatic dpi_export();
    #5;
    completed++;
  endtask
  initial begin
    fork
      begin
        victim = process::self();
        imp();
        completed++;
      end
    join_none
    #1;
    victim.kill();
    #10;
    `checkd(completed, 0);
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
