// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  process proc;

  initial begin
    fork
      begin
        proc = process::self();
        #1;
      end
      #10;
    join_any

    if (proc.status() != process::FINISHED) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
