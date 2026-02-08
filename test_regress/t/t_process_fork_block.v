// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
  process job;

  initial begin
    automatic process p1 = process::self();
    fork
      begin
        wait (p1.status() != process::RUNNING);
        $write("job started\n");
        job = process::self();
      end
    join_none
    wait (job);
    $write("all jobs started\n");
    job.await();
    $write("all jobs finished\n");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
