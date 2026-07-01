// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int cnt = 0;
  task automatic myTask;
    fork
      begin
        bit x;
        if (!x) begin
          cnt++;
        end
        if (!$onehot(x)) begin
          cnt++;
        end
      end
    join_none
  endtask

  initial begin
    myTask();
    #1;
    if (cnt != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
