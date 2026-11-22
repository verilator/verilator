// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  initial begin
    // Uses the std package, which gets no coverage points
    automatic process p = process::self();
    automatic mailbox #(int) mb = new;
    automatic semaphore sem = new(1);
    automatic int i;
    mb.put(1);
    void'(mb.try_get(i));
    sem.get(1);
    sem.put(1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
