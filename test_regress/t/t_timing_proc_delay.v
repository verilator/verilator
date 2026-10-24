// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Equal-time #delay waiters: process status across VlCoroutineHandle moves.

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); $stop; end while(0);
// verilog_format: on

module t;
  localparam int N = 64;
  process procs[N];
  int wake_order[N];
  int wake_n = 0;

  task automatic waiter(int id);
    procs[id] = process::self();
    #5;
    wake_order[wake_n++] = id;
  endtask

  initial begin
    for (int i = 0; i < N; i++) begin
      automatic int id = i;
      fork
        waiter(id);
      join_none
    end
    #0;
    for (int i = 0; i < N; i++) `checkd(procs[i].status(), process::WAITING);

    procs[N/2].kill();
    `checkd(procs[N/2].status(), process::KILLED);

    #5;
    #0;
    `checkd(wake_n, N - 1);
    for (int i = 0; i < N; i++) begin
      if (i == N / 2) begin
        `checkd(procs[i].status(), process::KILLED);
      end
      else begin
        `checkd(procs[i].status(), process::FINISHED);
      end
    end
    begin
      automatic int expect_id = 0;
      for (int k = 0; k < wake_n; k++) begin
        if (expect_id == N / 2) expect_id++;
        `checkd(wake_order[k], expect_id);
        expect_id++;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial #20 $stop;
endmodule
