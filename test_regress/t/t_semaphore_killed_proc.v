// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  semaphore sem = new(0);
  process first_waiter;
  process second_waiter;
  bit acquired;

  initial begin
    fork
      begin
        first_waiter = process::self();
        sem.get(1);
        $stop;
      end
      begin
        second_waiter = process::self();
        sem.get(1);
        acquired = 1;
      end
    join_none

    wait (first_waiter != null && second_waiter != null);
    #1;
    first_waiter.kill();
    sem.put(1);

    #1;
    if (!acquired) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
