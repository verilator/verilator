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
        fork
          begin
            #5;
          end
        join_none
        #1;
      end
      #10;
    join_any

    #1;
    if (proc.status() != process::FINISHED) $stop;
    disable fork;
    if (proc.status() != process::FINISHED) $stop;

    proc.kill();
    if (proc.status() != process::FINISHED) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
